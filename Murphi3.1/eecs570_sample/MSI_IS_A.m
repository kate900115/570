-- Three-state 3-hop MSI protocol

----------------------------------------------------------------------
-- Constants
----------------------------------------------------------------------
const
  ProcCount: 3;          -- number processors
  ValueCount:   2;       -- number of data values.
  VC0: 0;                -- low priority
  VC1: 1;
  VC2: 2;
  VC3: 3;
  VC4: 4;
  VC5: 5;
  QMax: 2;
  NumVCs: VC5 - VC0 + 1;
  NetMax: ProcCount+1;
  

----------------------------------------------------------------------
-- Types
----------------------------------------------------------------------
type
  Proc: scalarset(ProcCount);   -- unordered range of processors -- array type is ordered so we do not use array
  Value: scalarset(ValueCount); -- arbitrary values for tracking coherence
  Home: enum { HomeType };      -- need enumeration for IsMember calls
  Node: union { Home , Proc };

  VCType: VC0..NumVCs-1;
  
  ShareCnt: 0..ProcCount; 
  AckCnt: 0..ProcCount; 

  MessageType: enum {  GetS,            -- request for data . vc1
                       GetM,            -- request for data, and will modified that data. vc1
                       
                       Fwd_GetS,		-- the home node is not the owner, instead other Proc is the owner vc1
                       Fwd_GetM,
                       
                       Invalidation,	-- vc1	
                       Data,			-- to indicate the message is data.      vc3
                                             
					   PutS,            -- writeback the data in share state.    vc1
					   PutM,            -- writeback the data in modified state. vc1
                           
                       Put_Ack,			-- respond from home node to indicate the value is successful writeback.  vc2  
                       Inv_Ack 		    -- respond from other proc to indicate the block is invalidated. vc2
                    };

  Message:
    Record
      mtype: MessageType;
      src: Node;
      -- do not need a destination for verification; the destination is indicated by which array entry in the Net the message is placed
      
      vc: VCType;
      val: Value;
      -- indicate the index of nodes in the sharer's state
      sharenum: ShareCnt;
      
    End;

  HomeState:
    Record
      state: enum { H_Invalid, H_Modified, H_Shared, 					--stable states
      							HT_Pending }; 							--transient states during recall
      owner: Node;	
      sharers: multiset [ProcCount] of Node;    						
      val: Value; 
    End;

  ProcState:
    Record
      state: enum { P_Invalid, P_Shared, P_Modified, 					--stable states
                  IS_D, IM_AD, IM_A, IS_A, SM_AD, SM_A, MI_A, SI_A, II_A			--transient states
                  };
      val: Value;
      AckNum: AckCnt;
    End;

----------------------------------------------------------------------
-- Variables
----------------------------------------------------------------------
var
  HomeNode:  HomeState;
  Procs: array [Proc] of ProcState;
  Net:   array [Node] of multiset [NetMax] of Message;  				-- One multiset for each destination - messages are arbitrarily reordered by the multiset
  InBox: array [Node] of array [VCType] of Message; 					-- If a message is not processed, it is placed in InBox, blocking that virtual channel
  msg_processed: boolean;
  LastWrite: Value; 													-- Used to confirm that writes are not lost; this variable would not exist in real hardware

----------------------------------------------------------------------
-- Procedures
----------------------------------------------------------------------
Procedure Send(mtype:MessageType;
	           dst:Node;    --destination node
	           src:Node;	--sourse node
               vc:VCType;
               val:Value;
               scnt: ShareCnt
         );
var msg:Message;
Begin
  Assert (MultiSetCount(i:Net[dst], true) < NetMax) "Too many messages";
  msg.mtype := mtype;
  msg.src   := src;
  msg.vc    := vc;
  msg.val   := val;
  msg.sharenum := scnt;
  MultiSetAdd(msg, Net[dst]);
End;

Procedure ErrorUnhandledMsg(msg:Message; n:Node);
Begin
  error "Unhandled message type!";
End;

Procedure ErrorUnhandledState();
Begin
  error "Unhandled state!";
End;



Procedure AddToSharersList(n:Node);
Begin
  if MultiSetCount(i:HomeNode.sharers, HomeNode.sharers[i] = n) = 0
  then
    MultiSetAdd(n, HomeNode.sharers);
  endif;
End;



Function IsSharer(n:Node) : Boolean;
Begin
  return MultiSetCount(i:HomeNode.sharers, HomeNode.sharers[i] = n) > 0
End;



Procedure RemoveFromSharersList(n:Node);
Begin
  MultiSetRemovePred(i:HomeNode.sharers, HomeNode.sharers[i] = n);
End;


Procedure RemoveAllSharers();
Begin
	for n:Node do
	  if (IsMember(n, Proc) &
        MultiSetCount(i:HomeNode.sharers, HomeNode.sharers[i] = n) != 0)
	  then 
		RemoveFromSharersList(n);
	  endif;
	endfor;
End;


-- Sends a message to all sharers except rqst
Procedure SendInvReqToSharers(rqst:Node);
Begin
  for n:Node do
    if (IsMember(n, Proc) &
        MultiSetCount(i:HomeNode.sharers, HomeNode.sharers[i] = n) != 0)
    then
      if n != rqst
      then 
      	Send(Invalidation, n, rqst, VC2, UNDEFINED,0);
        -- Send invalidation message here 
      endif;
    endif;
  endfor;
End;



Procedure HomeReceive(msg:Message);
var cnt:0..ProcCount;  -- for counting sharers
Begin
-- Debug output may be helpful:
--  put "Receiving "; put msg.mtype; put " on VC"; put msg.vc; 
--  put " at home -- "; put HomeNode.state;

  -- The line below is not needed in Valid/Invalid protocol.  However, the 
  -- compiler barfs if we put this inside a switch, so it is useful to
  -- pre-calculate the sharer count here
  
  cnt := MultiSetCount(i:HomeNode.sharers, true);


  -- default to 'processing' message.  set to false otherwise
  msg_processed := true;

  switch HomeNode.state
  
  case H_Invalid:                      
  --H_Invalid means that there is no other node who has the value.
    switch msg.mtype

    case GetS:
      HomeNode.state := H_Shared;
      AddToSharersList(msg.src);
      Send(Data, msg.src, HomeType, VC4, HomeNode.val, 0);
      
    case GetM:
	  HomeNode.state := H_Modified;
      HomeNode.owner := msg.src;
      Send(Data, msg.src, HomeType, VC4, HomeNode.val, 0);	 
     
    case PutS:
      Send(Put_Ack, msg.src, HomeType, VC1, UNDEFINED, 0);
    
    case PutM:
    -- Initial State: Proc0 is in M, Proc1 is I, Dir is M
    -- (1) Proc1 issues a GetM
    -- (2) Directory issues FwdGetM and Proc0 simultaneously evicts with a PutM. A really really slow PutM...
    -- (3) The FwdGetM reaches Proc0 and is serviced because it's in the MIa state
    -- (4) Proc1 (new owner) receives data from Proc0 and is able to evict by issuing it's own PutM.
    -- (5) If the PutM from Proc1 gets to the Dir before PutM in step 2, then the directory will be in the Invalid state by the time the 2nd one arrives
    
       if (IsUnDefined(HomeNode.owner))
       then
       		Send(Put_Ack, msg.src, HomeType, VC1, UNDEFINED, 0);
       endif;
      
    else
      ErrorUnhandledMsg(msg, HomeType);

  endswitch;

  case H_Shared:							
  --H_Valid means that there is other node who has the value.
  --That node should return the value to the requesting node.
   Assert !(cnt = 0) 
    "HomeNode has no sharer, but line is Valid";

    switch msg.mtype
    case GetS:     
      Send(Data, msg.src, HomeType, VC4, HomeNode.val, 0);
      AddToSharersList(msg.src);
            
    case GetM:
      if (cnt = 1)
      then
        if (IsSharer(msg.src))
        then
          Send(Data, msg.src, HomeType, VC4, HomeNode.val, 0);
        else
          Send(Data, msg.src, HomeType, VC4, HomeNode.val, cnt);
        endif;
      else
        Send(Data, msg.src, HomeType, VC4, HomeNode.val, cnt);
      endif;
      
      
	  SendInvReqToSharers(msg.src);
	  HomeNode.owner := msg.src;
	  -- clear shares
	  RemoveAllSharers();
	  HomeNode.state := H_Modified;
	  
	case PutS:
	  Send(Put_Ack, msg.src, HomeType, VC1, UNDEFINED, 0);
	  if (cnt=1)
	  then 
	    if IsSharer(msg.src)
	    then
	  	  HomeNode.state := H_Invalid; 
	  	endif;
	  endif;
	  RemoveFromSharersList(msg.src);
      
    case PutM:
      if (IsUnDefined(HomeNode.owner))
      then
        if (cnt =1)
        then
          if IsSharer(msg.src)
          then
            HomeNode.state := H_Invalid;
          endif;
        endif;

        RemoveFromSharersList(msg.src);
       	Send(Put_Ack, msg.src, HomeType, VC1, UNDEFINED, 0);
      endif;
      
    else
      ErrorUnhandledMsg(msg, HomeType);

    endswitch;

  case H_Modified:
    switch msg.mtype
   
    case GetS:
      Assert (!IsUnDefined(HomeNode.owner)) "owner undefined";
      AddToSharersList(msg.src);
      AddToSharersList(HomeNode.owner);
      Send(Fwd_GetS, HomeNode.owner, msg.src, VC1, UNDEFINED, 0);
      HomeNode.state := HT_Pending;
		--Home node is waiting for the data to be sent back from the modified node
	  undefine HomeNode.owner;
	  
    case GetM:
      Assert (!IsUnDefined(HomeNode.owner)) "owner undefined";
      --Send(Fwd_GetM, HomeNode.owner, msg.src, VC1, UNDEFINED, 0);
      Send(Fwd_GetM, HomeNode.owner, msg.src, VC1, UNDEFINED, 0);
      HomeNode.owner := msg.src;
      
    case PutS:
      Send(Put_Ack, msg.src, HomeType, VC1, UNDEFINED, 0);

	case PutM:
	  if !(HomeNode.owner=msg.src)
	  then
	    --msg_processed := false;
	    --doing nothing at all
	    --Send(Put_Ack, msg.src, HomeType, VC1, UNDEFINED, 0);
	  endif;
	  if (HomeNode.owner=msg.src)
	  then
	    HomeNode.state := H_Invalid;
	    HomeNode.val   := msg.val;
	    undefine HomeNode.owner;
	    Send(Put_Ack, msg.src, HomeType, VC1, UNDEFINED, 0);
	  endif;
	  
	
    else
      ErrorUnhandledMsg(msg, HomeType);

    endswitch;
    
  case HT_Pending: 
	switch msg.mtype
	
	case GetS:
	  msg_processed := false;
	  
	case GetM:
	  msg_processed := false;
	
	case PutS:
	  RemoveFromSharersList(msg.src);
	  Send(Put_Ack, msg.src, HomeType, VC1, UNDEFINED, 0);
		
	case PutM:
      if !(HomeNode.owner = msg.src)
      then
      	msg_processed := false;
	  	--RemoveFromSharersList(msg.src);
	  	--Send(Put_Ack, msg.src, HomeType, VC1, UNDEFINED, 0);
	  --else
	    --ErrorUnhandledMsg(msg, HomeType);
	  endif;
	  
    case Data:
      HomeNode.val := msg.val;
      if !(cnt=0)
      then
        HomeNode.state:= H_Shared;
      endif;
     
	else
	  ErrorUnhandledMsg(msg, HomeType);
	  
  endswitch;  
  endswitch;
End;




Procedure ProcReceive(msg:Message; p:Proc);
Begin
--  put "Receiving "; put msg.mtype; put " on VC"; put msg.vc; 
--  put " at proc "; put p; put "\n";

   -- default to 'processing' message.  set to false otherwise
  msg_processed := true;

  alias ps:Procs[p].state do
  alias pv:Procs[p].val do
  alias pan:Procs[p].AckNum do  
  
  switch ps
  case P_Invalid:
    switch msg.mtype
      case Invalidation:
        Send(Inv_Ack, msg.src, p, VC5, UNDEFINED, 0);
        
      else
         ErrorUnhandledMsg(msg, p);
  endswitch;
  
  case P_Shared:
    switch msg.mtype	 
	  case Invalidation:
		 ps := P_Invalid;
		 undefine pv;
		 Send(Inv_Ack, msg.src, p, VC5, UNDEFINED, 0);

      else
         ErrorUnhandledMsg(msg, p);
  endswitch;

  case P_Modified: 
    switch msg.mtype
      case Fwd_GetS:
        Send(Data, msg.src, p, VC4, pv, 0);
        Send(Data, HomeType, p, VC4, pv, 0);
        ps := P_Shared;
        
      case Fwd_GetM:
      	Send(Data, msg.src, p, VC4, pv, 0);
      	ps := P_Invalid;
      	undefine pv;
		  
	  else
        ErrorUnhandledMsg(msg, p);
    endswitch;
  
  case IS_D:
  	switch msg.mtype
  	  case Invalidation:
  	    msg_processed := false;
  	    
  	  case Data:
  	    if (msg.src = HomeType)
  	    then
  	      if (msg.sharenum = 0)
  	      then
  	      	ps := P_Shared;
  	      	pv := msg.val;
  	      endif;
  	    endif;
  	    
  	    if !(msg.src = HomeType)
  	    then
  	    	ps := P_Shared;
  	    	pv := msg.val;
  	    endif;
  	   
  	  else
        ErrorUnhandledMsg(msg, p);
        
    endswitch;

  case IM_AD:
    switch msg.mtype
      case Invalidation:
        --doing nothing at all ;
      case Fwd_GetS:
        msg_processed := false;
       
      case Fwd_GetM:
        msg_processed := false;
        
      case Data:
        if (msg.src = HomeType)
        then
          if (msg.sharenum = 0)
          then
            ps := P_Modified;
            pv := msg.val;
          endif;
          if (msg.sharenum > 0)
          then
            ps := IM_A;
            pan:= msg.sharenum;
            pv := msg.val;
          endif;
        endif;
 
        if !(msg.src = HomeType)
        then
          ps := P_Modified;
          pv := msg.val;
        endif;
      
      case Inv_Ack:
		-- pan := pan - 1; 
		-- I believe there should be a stall
		-- Instead of ack-- (in the textbook)
		msg_processed := false;
     
      else
        ErrorUnhandledMsg(msg, p);
        
      endswitch;
	  
  case IM_A:
    switch msg.mtype  
      case Fwd_GetS:
        Send(Data, msg.src, p, VC4, pv, 0);
        Send(Data, HomeType, p, VC4, pv, 0);
        ps := IS_A;
        
        --msg_processed := false;
        
      case Fwd_GetM:
        msg_processed := false;
      
      case Inv_Ack:
        if (pan=1)
        then
          ps := P_Modified;
        endif;
        pan := pan - 1; 
        
      case Invalidation:
        Send(Inv_Ack, msg.src, p, VC5, UNDEFINED, 0);
        
      else
        ErrorUnhandledMsg(msg, p);
        
    endswitch;
  case IS_A:
    switch msg.mtype
      case Inv_Ack:
        if (pan=1)
        then
          ps := P_Shared;
        endif;
        pan := pan - 1; 

      else
        msg_processed := false;
    endswitch;
  
  case SM_AD:
    switch msg.mtype
      case Fwd_GetS:
        msg_processed := false;
        
      case Fwd_GetM:
        msg_processed := false;
        
      case Invalidation:
        Send(Inv_Ack, msg.src, p, VC5, UNDEFINED, 0);
        ps := IM_AD;
        
      case Data:
        if (msg.src = HomeType)
        then 
          if (msg.sharenum = 0)
          then
            ps := P_Modified;
            pv := msg.val;
          endif;
          
          if (msg.sharenum > 0)
          then
            ps := SM_A;
            pan:= msg.sharenum;
            pv := msg.val;
          endif;
        endif;
        
        if !(msg.src = HomeType)
        then
          ps := P_Modified;
          pv := msg.val;
        endif;
        
      case Inv_Ack:
        -- pan := pan - 1; 
        -- In the textbook, it says the state should not change and ack--
        -- But I think there should be a stall
        msg_processed := false;
        
      else
        ErrorUnhandledMsg(msg, p);
        
    endswitch;  
    
  case SM_A:
    switch msg.mtype
      case Invalidation:
        ps := IM_A;
    
      case Fwd_GetS:
        msg_processed := false;
        
      case Fwd_GetM:
        msg_processed := false;
        
      case Inv_Ack:
        if (pan = 1)
        then 
          ps := P_Modified;
        endif;
        pan := pan -1;
        
      
      else
        ErrorUnhandledMsg(msg, p);
        
    endswitch;  
      
  case MI_A:
    switch msg.mtype
      case Fwd_GetS:
        Send(Data, msg.src, p, VC4, pv, 0);
        Send(Data, HomeType, p, VC4, pv, 0);
        ps := SI_A;
        
      case Fwd_GetM:
        Send(Data, msg.src, p, VC4, pv, 0);
        ps := II_A;
        
      case Put_Ack:
        ps := P_Invalid;
        undefine pv;
        
      else
        ErrorUnhandledMsg(msg, p);
        
    endswitch;  
    
  case SI_A:
    switch msg.mtype
      case Invalidation:
        Send(Inv_Ack, msg.src, p, VC5, UNDEFINED, 0);
        ps := II_A;
      
      case Put_Ack:
        ps := P_Invalid;
        undefine pv;
      
      else
        ErrorUnhandledMsg(msg, p);
        
    endswitch;  
    
  case II_A:
    switch msg.mtype
      case Put_Ack:
        ps := P_Invalid;
        undefine pv;
        
    else
        ErrorUnhandledMsg(msg, p);
        
    endswitch;   
  endswitch;

  endalias;
  endalias;
  endalias;
End;

----------------------------------------------------------------------
-- Rules
----------------------------------------------------------------------

-- Processor actions (affecting coherency)

ruleset n:Proc Do
  alias p:Procs[n] Do

	ruleset v:Value Do
  	  rule "store new value"
   	   
 	    if (p.state = P_Modified)
 	    then
 	      p.val := v;
 	      LastWrite := v; --We use LastWrite to sanity check that reads receive the value of the last write
 	    endif;
 	  
      endrule;
	endruleset;
	
	rule "write request"
	    if (p.state = P_Invalid)
        then
          Send(GetM, HomeType, n, VC0, UNDEFINED, 0);
 		  p.state := IM_AD;  
 	    endif;
 	    if (p.state = P_Shared)
 	    then
 	      Send(GetM, HomeType, n, VC0, UNDEFINED, 0);
 		  p.state := SM_AD;  
 	    endif;
 	endrule;

    rule "read request"
      p.state = P_Invalid
      ==>
        Send(GetS, HomeType, n, VC0, UNDEFINED, 0);
        p.state := IS_D;
    endrule;
    
    rule "replacement(writeback)"
      if (p.state = P_Shared)
      then
        Send(PutS, HomeType, n, VC0, UNDEFINED, 0);
        p.state := SI_A;
      endif;
      if (p.state = P_Modified)
      then
        Send(PutM, HomeType, n, VC0, p.val, 0);
        p.state := MI_A;
      endif;
    endrule;

  endalias;
endruleset;

-- Message delivery rules
ruleset n:Node do
  choose midx:Net[n] do
    alias chan:Net[n] do
    alias msg:chan[midx] do
    alias box:InBox[n] do

		-- Pick a random message in the network and delivier it
    rule "receive-net"
			(isundefined(box[msg.vc].mtype))
    ==>

      if IsMember(n, Home)
      then
        HomeReceive(msg);
      else
        ProcReceive(msg, n);
			endif;

			if ! msg_processed
			then
				-- The node refused the message, stick it in the InBox to block the VC.
	  		box[msg.vc] := msg;
			endif;
	  
		  MultiSetRemove(midx, chan);
	  
    endrule;
  
    endalias
    endalias;
    endalias;
  endchoose;  

	-- Try to deliver a message from a blocked VC; perhaps the node can handle it now
	ruleset vc:VCType do
    rule "receive-blocked-vc"
			(! isundefined(InBox[n][vc].mtype))
    ==>
      if IsMember(n, Home)
      then
        HomeReceive(InBox[n][vc]);
      else
        ProcReceive(InBox[n][vc], n);
	  endif;

			if msg_processed
			then
				-- Message has been handled, forget it
	  		undefine InBox[n][vc];
			endif;
	  
    endrule;
  endruleset;

endruleset;

----------------------------------------------------------------------
-- Startstate
----------------------------------------------------------------------
startstate

	For v:Value do
  -- home node initialization
  HomeNode.state := H_Invalid;
  undefine HomeNode.owner;
  undefine HomeNode.sharers;
  HomeNode.val := v;
	endfor;
	LastWrite := HomeNode.val;
  
  -- processor initialization
  for i:Proc do
    Procs[i].state := P_Invalid;
    undefine Procs[i].val;
    Procs[i].AckNum := 0;
  endfor;

  -- network initialization
  undefine Net;
endstartstate;

----------------------------------------------------------------------
-- Invariants
----------------------------------------------------------------------

invariant "Invalid implies empty owner"
  HomeNode.state = H_Invalid
    ->
      IsUndefined(HomeNode.owner);

invariant "value in memory matches value of last write, when invalid"
     HomeNode.state = H_Invalid 
    ->
			HomeNode.val = LastWrite;

invariant "values in modified state match last write"
  Forall n : Proc Do	
     Procs[n].state = P_Modified
    ->
			Procs[n].val = LastWrite --LastWrite is updated whenever a new value is created 
	end;
	
invariant "value is undefined while invalid"
  Forall n : Proc Do	
     Procs[n].state = P_Invalid
    ->
			IsUndefined(Procs[n].val)
	end;
	
	
-- Here are some invariants that are helpful for validating shared state.

invariant "modified implies empty sharers list"
  HomeNode.state = H_Modified
    ->
      MultiSetCount(i:HomeNode.sharers, true) = 0;

invariant "Invalid implies empty sharer list"
  HomeNode.state = H_Invalid
    ->
      MultiSetCount(i:HomeNode.sharers, true) = 0;

invariant "values in memory matches value of last write, when shared or invalid"
  Forall n : Proc Do	
     HomeNode.state = H_Shared | HomeNode.state = H_Invalid
    ->
			HomeNode.val = LastWrite
	end;

invariant "values in shared state match memory"
  Forall n : Proc Do	
     HomeNode.state = H_Shared & Procs[n].state = P_Shared
    ->
			HomeNode.val = Procs[n].val
	end;
