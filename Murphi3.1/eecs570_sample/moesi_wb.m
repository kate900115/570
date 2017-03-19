-- Four-state 3-hop MESI protocol

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
  VC6: 6;
  VC7: 7;
  VC8: 8;
  QMax: 2;
  NumVCs: VC8 - VC0 + 1;
  NetMax: 2*ProcCount+1;
  

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
  InvAckCnt: 0..ProcCount; 
  FwdAckCnt: 0..ProcCount; 

  MessageType: enum {  GetS,            -- request for data . 
                       GetM,            -- request for data, and will modified that data.
                       
                       Fwd_GetS,		-- the home node is not the owner, instead other Proc is the owner 
                       Fwd_GetM,
                       
                       Invalidation,	-- vc1	
                       Data,			-- to indicate the message is data.      
                       ExcData,			-- Exclusive Data.
			NullData,
			FwdData,
                                             
			PutS,            -- writeback the data in share state.    
			PutM,            -- writeback the data in modified state. 
                       PutE,
			PutO,
                       Put_Ack,			-- respond from home node to indicate the value is successful writeback.  
                       Inv_Ack, 		    -- respond from other proc to indicate the block is invalidated.
                       Fwd_Ack,
			Put_Ack_S,
			GetM_Ack,
	 		OwnedData
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
      state: enum { H_Invalid, H_Modified, H_Shared, H_Exclusive, H_Owned,	--stable states
      		    H_SM_A, H_MS_D, H_EM_A, H_MM_A, H_OI_A, H_OM_A, H_MO_A, H_OO_A }; 		--transient states during recall
      owner: Node;	
      sharers: multiset [ProcCount] of Node;    						
      val: Value; 
    End;

  ProcState:
    Record
      state: enum { P_Invalid, P_Shared, P_Modified, P_Exclusive, P_Owned,			--stable states
                  IS_D, IM_AD, IM_A, SM_AD, SM_A, MI_A,EI_A, SI_A, OI_A_WaitForFwdAck, II_A, OI_A_WaitForPutAck, OI_A, OM_A, OM_A_WaitForGetMAck, OM_A_WaitForInvAck, OO_A,IM_AD_WaitForGetMAck, OI_A_WaitForGetMAck			--transient states
                  };
      val: Value;
      InvAckNum: InvAckCnt;
      FwdAckNum: FwdAckCnt;
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
      HomeNode.state := H_Exclusive;
      HomeNode.owner := msg.src;
      Send(ExcData, msg.src, HomeType, VC4, HomeNode.val, 0);
      
    case GetM:
	  HomeNode.state := H_Modified;
      HomeNode.owner := msg.src;
      Send(Data, msg.src, HomeType, VC4, HomeNode.val, 0);	 
     
    case PutS:
      Send(Put_Ack, msg.src, HomeType, VC1, UNDEFINED, 0);
    
    case PutM:
    -- Initial State: Proc0 is in M, Proc1 is I, Dir is M 
       if (HomeNode.owner=msg.src)
	   then
	     ErrorUnhandledMsg(msg, HomeType);
	   else
       	 Send(Put_Ack, msg.src, HomeType, VC1, UNDEFINED, 0);
       endif;

    case PutE:
      if !(HomeNode.owner = msg.src)
	  then 
        Send(Put_Ack, msg.src, HomeType, VC1, UNDEFINED, 0);
      endif;
	
    case PutO:
      if !(HomeNode.owner = msg.src)
	  then 
        Send(Put_Ack, msg.src, HomeType, VC1, UNDEFINED, 0);
      endif;

    case Fwd_Ack:
      --doing nothing at all
    case Inv_Ack:
      
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
	  -- RemoveAllSharersi();
	  HomeNode.state := H_SM_A;
	  
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
      if !(HomeNode.owner=msg.src)
      then
        if (cnt =1)
        then
          if IsSharer(msg.src)
          then
            HomeNode.state := H_Invalid;
          endif;
		endif;
	  else
	    ErrorUnhandledMsg(msg, HomeType);
	  endif;

      RemoveFromSharersList(msg.src);
      Send(Put_Ack, msg.src, HomeType, VC1, UNDEFINED, 0);
   

	case PutE:
	  if (HomeNode.owner = msg.src)
	  then
        RemoveFromSharersList(msg.src);
		Send(Put_Ack, msg.src, HomeType, VC1, UNDEFINED, 0);
      else
        if IsSharer(msg.src)
        then
          if (cnt = 1)
          then
            HomeNode.state := H_Invalid;
          endif;
          RemoveFromSharersList(msg.src);
          Send(Put_Ack, msg.src, HomeType, VC1, UNDEFINED, 0);
        else
          Send(Put_Ack, msg.src, HomeType, VC1, UNDEFINED, 0);
        endif;
	  endif;

    case Fwd_Ack:
      --doing nothing at all

    else
      ErrorUnhandledMsg(msg, HomeType);

    endswitch;

  case H_Exclusive:
	switch msg.mtype
	  case GetS:
		Send(Fwd_GetS, HomeNode.owner, msg.src, VC3, UNDEFINED, 0);
		AddToSharersList(msg.src);
		HomeNode.state := H_MO_A;

	  case GetM:
		Send(Fwd_GetM, HomeNode.owner, msg.src, VC3, UNDEFINED, 0);-----------------------
		HomeNode.owner := msg.src;
		HomeNode.state := H_EM_A;
	 
	  case PutS:
	    Send(Put_Ack, msg.src, HomeType, VC1, UNDEFINED, 0);

	  case PutM:
	    if(HomeNode.owner = msg.src)
		then
		  Send(Put_Ack, msg.src, HomeType, VC1, UNDEFINED, 0);
		  undefine HomeNode.owner;
		  HomeNode.state := H_Invalid;
		  HomeNode.val := msg.val;
	    else
		  Send(Put_Ack, msg.src, HomeType, VC1, UNDEFINED, 0);
	    endif;
	    
	  case PutE:
	    if (HomeNode.owner = msg.src)
	    then
	      Send(Put_Ack, msg.src, HomeType, VC1, UNDEFINED, 0);
	      undefine HomeNode.owner;
	      HomeNode.state := H_Invalid;
	    else
              Send(Put_Ack, msg.src, HomeType, VC1, UNDEFINED, 0);
	    endif;

	  case PutO:
            if !(HomeNode.owner=msg.src)
            then
              Send(Put_Ack, msg.src, HomeType, VC1, UNDEFINED, 0);
            endif;

          case Fwd_Ack:
        	--doing nothing at all

	  else
      	    ErrorUnhandledMsg(msg, HomeType);
	endswitch;
        

  case H_Modified:
    switch msg.mtype
   
    case GetS:
      Assert (!IsUnDefined(HomeNode.owner)) "owner undefined";
      AddToSharersList(msg.src);
      Send(Fwd_GetS, HomeNode.owner, msg.src, VC3, UNDEFINED, 0);
      HomeNode.state := H_MO_A;
		--Home node is waiting for the data to be sent back from the modified node
	  
    case GetM:
      Assert (!IsUnDefined(HomeNode.owner)) "owner undefined";
      Send(Fwd_GetM, HomeNode.owner, msg.src, VC1, UNDEFINED, 0);
      HomeNode.owner := msg.src;
      HomeNode.state := H_MM_A;

    case PutS:
      Send(Put_Ack, msg.src, HomeType, VC1, UNDEFINED, 0);
      
    case PutE:
      Send(Put_Ack, msg.src, HomeType, VC1, UNDEFINED, 0);

    case PutM:
      if (HomeNode.owner=msg.src)
      then
	HomeNode.state := H_Invalid;
	HomeNode.val   := msg.val;
	undefine HomeNode.owner;
	Send(Put_Ack, msg.src, HomeType, VC1, UNDEFINED, 0);
      endif;
    
    case PutO:
      if !(HomeNode.owner=msg.src)
      then
        Send(Put_Ack, msg.src, HomeType, VC1, UNDEFINED, 0);
      endif;

    case Fwd_Ack:
	  
    else
      ErrorUnhandledMsg(msg, HomeType);

    endswitch;
    

  case H_Owned:
    switch msg.mtype
      case GetS:
	    Send(Fwd_GetS, HomeNode.owner, msg.src, VC3, UNDEFINED, cnt);
	    AddToSharersList(msg.src);
	    HomeNode.state:=H_OO_A;
      case GetM:
	if (msg.src=HomeNode.owner)
	then
	  Send(GetM_Ack, msg.src, HomeType, VC3, UNDEFINED, cnt);
	  if (cnt =0)
	  then
	    HomeNode.state:=H_OM_A;
	  else
	    SendInvReqToSharers(msg.src);
	    HomeNode.state:=H_OM_A;
	  endif;
	else
	    if (IsSharer(msg.src))
	    then
	      RemoveFromSharersList(msg.src);
	      cnt := cnt-1;
	    endif;
	    
	    Send(Fwd_GetM, HomeNode.owner, msg.src, VC3, UNDEFINED, cnt);
	    SendInvReqToSharers(msg.src);
	    HomeNode.owner:=msg.src;
	    HomeNode.state:=H_OM_A;
	endif;
      case PutS:
	    Send(Put_Ack, msg.src, HomeType, VC1, UNDEFINED, 0);
	    RemoveFromSharersList(msg.src);
      case PutE:
	if (cnt=0)
	then		
	  Send(Put_Ack, msg.src, HomeType, VC1, UNDEFINED, 0);
	  if (msg.src=HomeNode.owner)
	  then
	    HomeNode.state := H_Invalid;
            undefine HomeNode.owner;
	  endif;
	else
	  Send(Put_Ack_S, msg.src, HomeType, VC1, UNDEFINED, cnt);
	endif;
	if (msg.src = HomeNode.owner)
	then
	  HomeNode.state := H_OI_A;
	  undefine HomeNode.owner;
	  SendInvReqToSharers(msg.src);
	endif;


      case PutO:
	if (cnt>0)
	then
	  Send(Put_Ack_S, msg.src, HomeType, VC1, UNDEFINED, cnt);
	  if (msg.src = HomeNode.owner)
	  then
	    HomeNode.val := msg.val;
	    HomeNode.state := H_OI_A;
	    undefine HomeNode.owner;
	    SendInvReqToSharers(msg.src);
	  endif;
	endif;
	if (cnt = 0)
	then
	  Send(Put_Ack, msg.src, HomeType, VC1, UNDEFINED, 0);
 	  if (msg.src = HomeNode.owner)
	  then
	    HomeNode.val := msg.val;
	    HomeNode.state := H_Invalid;
	    undefine HomeNode.owner;
	  endif;
	endif;


      case PutM:
	if (cnt>0)
	then
	  Send(Put_Ack_S, msg.src, HomeType, VC1, UNDEFINED, cnt);
	  if (msg.src = HomeNode.owner)
	  then
	    HomeNode.val := msg.val;
	    HomeNode.state := H_OI_A;
	    undefine HomeNode.owner;
	    SendInvReqToSharers(msg.src);
	  endif;
	endif;
	if (cnt = 0)
	then
	  Send(Put_Ack, msg.src, HomeType, VC1, UNDEFINED, 0);
 	  if (msg.src = HomeNode.owner)
	  then
	    HomeNode.val := msg.val;
	    HomeNode.state := H_Invalid;
	    undefine HomeNode.owner;
	  endif;
	endif;
	
      else
        ErrorUnhandledMsg(msg, HomeType);

    endswitch;
    
   
  case H_SM_A:
    switch msg.mtype
      case Inv_Ack:
        if (cnt = 1)
        then 
          HomeNode.state := H_Modified;
        endif;
        RemoveFromSharersList(msg.src);
      else
        msg_processed := false;
      endswitch;


  case H_EM_A:
    switch msg.mtype
      case PutE:
        msg_processed := false;
      case Fwd_Ack:
        --if (HomeNode.owner = msg.src)
        --then
        HomeNode.state := H_Modified;
        --endif;
      else
        msg_processed := false;
      endswitch;

  case H_MM_A:
    switch msg.mtype
      case PutE:
        msg_processed := false;
      case Fwd_Ack:
        --if (HomeNode.owner = msg.src)
        --then
        HomeNode.state := H_Modified;
        --endif;
      else
        msg_processed := false;
      endswitch;



  case H_MS_D:
	switch msg.mtype

	case GetS:
	  msg_processed := false;
	  
	case GetM:
	  msg_processed := false;
	  
	case Fwd_GetS:
	  msg_processed := false;
	  
	case Fwd_GetM:
	  msg_processed := false;
	  
	case PutE:
          msg_processed := false;
	  --Send(Put_Ack, msg.src, HomeType, VC1, UNDEFINED, 0);
	
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

        case Fwd_Ack:
          -- doing nothing at all
	  
        case Data:
          HomeNode.val := msg.val;
          if !(cnt=0)
          then
            HomeNode.state:= H_Shared;
          else
            HomeNode.state:= H_Invalid;
          endif;
     
	else
	  ErrorUnhandledMsg(msg, HomeType);
	  
    endswitch; 


  case H_OM_A:
    switch msg.mtype
    case Inv_Ack:
      if (cnt>1)
      then
        RemoveFromSharersList(msg.src);
      else 
	RemoveFromSharersList(msg.src);
	--HomeNode.state:= H_Modified;
      endif;
    case Fwd_Ack:
      if (cnt=0)
      then
	HomeNode.state:= H_Modified;
      else
	msg_processed := false;
      endif;
    else
      msg_processed := false;
    endswitch;

  case H_MO_A:
	switch msg.mtype
	case Fwd_Ack:
	  HomeNode.state:=H_Owned;
	else 
	  msg_processed := false;
	  --ErrorUnhandledMsg(msg, HomeType);
	endswitch;


  case H_OO_A:
    switch msg.mtype
    case Fwd_Ack:
	HomeNode.state:= H_Owned;
    case PutS:
	if (IsSharer(msg.src))
	then
	  RemoveFromSharersList(msg.src);
	endif;
	Send(Put_Ack, msg.src, HomeType, VC1, UNDEFINED, 0);
    else
      msg_processed := false;
    endswitch;


  case H_OI_A:
    switch msg.mtype
    case GetS:
      msg_processed := false;
    case Inv_Ack:
      if (cnt>0)
      then
        RemoveFromSharersList(msg.src);
      endif;
      if (cnt=1)
      then
        HomeNode.state:=H_Invalid;
      endif;
    else
	  msg_processed := false;
      --ErrorUnhandledMsg(msg, HomeType);
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
  alias pan:Procs[p].InvAckNum do  
  alias fan:Procs[p].FwdAckNum do
  
  switch ps
  case P_Invalid:
    switch msg.mtype
      case Invalidation:
        Send(Inv_Ack, msg.src, p, VC5, UNDEFINED, 0);
      case Fwd_GetS:
	Send(NullData, msg.src, p, VC4, pv, 0);
      case Inv_Ack:
      case Fwd_Ack:
        
      else
         ErrorUnhandledMsg(msg, p);
  endswitch;
  
  case P_Shared:
    switch msg.mtype	 
	  case Invalidation:
		 ps := P_Invalid;
		 undefine pv;
		 Send(Inv_Ack, msg.src, p, VC5, UNDEFINED, 0);
		 Send(Inv_Ack, HomeType, p, VC5, UNDEFINED, 0);

      else
         ErrorUnhandledMsg(msg, p);
  endswitch;

  case P_Modified: 
    switch msg.mtype
      case Fwd_GetS:
        Send(FwdData, msg.src, p, VC4, pv, 0);
	fan:=fan+1;
        ps := OO_A;
        
      case Fwd_GetM:
      	Send(Data, msg.src, p, VC4, pv, msg.sharenum);
        Send(Fwd_Ack, HomeType, p, VC7, UNDEFINED, 0);
      	ps := P_Invalid;
      	undefine pv;

      case Fwd_Ack:--------------------------------
		  
	  else
        ErrorUnhandledMsg(msg, p);
    endswitch;
    
  case P_Exclusive:
    switch msg.mtype
      case Fwd_GetS:
        Send(FwdData, msg.src, p, VC4, pv, 0);
	fan:= fan+1;
        --ps := P_Owned;
	ps:=OO_A;
        
      case Fwd_GetM:
        Send(Data, msg.src, p, VC4, pv, msg.sharenum);
        Send(Fwd_Ack, HomeType, p, VC7, UNDEFINED, 0);
        ps := P_Invalid;
        undefine pv;
        
      else
        ErrorUnhandledMsg(msg, p);
    endswitch;

  case P_Owned:
    switch msg.mtype
      case Fwd_GetS:
	--if (fan<ProcCount)
	if (fan=0)
	then
	  Send(FwdData, msg.src, p, VC4, pv, 0);
	  fan:=fan+1;
	  ps:=OO_A;
	else
	  msg_processed := false;
	endif;
        
      case Fwd_GetM:
	if (fan<ProcCount)
	then
        Send(FwdData, msg.src, p, VC4, pv, msg.sharenum);
        --Send(Fwd_Ack, HomeType, p, VC7, UNDEFINED, 0);
        --ps := P_Invalid;
	fan:=fan+1;
	ps := OI_A_WaitForFwdAck;
        undefine pv;
	else
	  msg_processed := false;
	endif;

      case Fwd_Ack:
	fan:=fan-1;

      else
        ErrorUnhandledMsg(msg, p);
    endswitch;
  
  case IS_D:
  	switch msg.mtype
  	  case Invalidation:
  	    msg_processed := false;
  	    
  	  case Fwd_GetS:
	    msg_processed := false;
	  
	  case Fwd_GetM:
	    msg_processed := false;
  	    
  	  case ExcData:
  	    ps := P_Exclusive;
  	    pv := msg.val;

	  case FwdData:
		ps := P_Shared;
		pv := msg.val;
		Send(Fwd_Ack, HomeType, p, VC7, UNDEFINED, 0);
	        Send(Fwd_Ack, msg.src, p, VC7, UNDEFINED, 0);
	case OwnedData:
	  --if (msg.sharenum>0)
	  --then
	  --  pan:=msg.sharenum;
	  --  Send(Fwd_Ack, HomeType, p, VC7, UNDEFINED, 0);
	  --  pv :=msg.val;
	   -- ps :=P_Shared;
	  --else
	    pv :=msg.val;
	    ps :=P_Shared;
	    Send(Fwd_Ack, HomeType, p, VC7, UNDEFINED, 0);
	  --endif;
  	    
  	  case Data:
  	    if (msg.src = HomeType)
  	    then
  	      if (msg.sharenum = 0)
  	      then
  	      	ps := P_Shared;
  	      	pv := msg.val;
  	      else
  	        ps := P_Shared;
  	      	pv := msg.val;
  	      endif;
  	    endif;
  	    
  	    if !(msg.src = HomeType)
  	    then
  	    	ps := P_Shared;
  	    	pv := msg.val;
  	    endif;
          case NullData:
	    Send(Inv_Ack, HomeType, p, VC5, UNDEFINED, 0);
  	    ps := P_Invalid;
	  case Inv_Ack:

	  case Fwd_Ack:

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
          pan:= msg.sharenum;
	  if (pan=0)
	  then
	    ps := P_Modified;
	  else
	    ps := IM_A;
	  endif;
          
          pv := msg.val;
        endif;
     
      case FwdData:
	if (msg.sharenum>0)
	then
	  pan:=msg.sharenum;
	  Send(Fwd_Ack, HomeType, p, VC7, UNDEFINED, 0);
	  Send(Fwd_Ack, msg.src, p, VC7, UNDEFINED, 0);
	  pv :=msg.val;
	  ps :=IM_A;
	else
	  pv :=msg.val;
	  ps :=P_Modified;
	  Send(Fwd_Ack, HomeType, p, VC7, UNDEFINED, 0);
	  Send(Fwd_Ack, msg.src, p, VC7, UNDEFINED, 0);
	endif;


      case OwnedData:
	if (msg.sharenum>0)
	then
	  pan:=msg.sharenum;
	  Send(Fwd_Ack, HomeType, p, VC7, UNDEFINED, 0);
	  pv :=msg.val;
	  ps :=IM_A;
	else
	  pv :=msg.val;
	  ps :=P_Modified;
	  Send(Fwd_Ack, HomeType, p, VC7, UNDEFINED, 0);
	endif;

      case Inv_Ack:
	msg_processed := false;

      case Fwd_Ack:
     
      else
        ErrorUnhandledMsg(msg, p);
        
      endswitch;
	  
  case IM_A:
    switch msg.mtype  
      case Fwd_GetS:
        msg_processed := false;
        
      case Fwd_GetM:
        msg_processed := false;
      
      case Inv_Ack:
        if (pan=1)
        then
          ps := P_Modified;
        endif;
        pan := pan - 1; 
        
        
      else
        ErrorUnhandledMsg(msg, p);
        
    endswitch;

  case OO_A:
    switch msg.mtype  
      case Fwd_Ack:
	if (fan>1)
	then
          fan:= fan-1;
	else
	  fan:=0;
	  ps:=P_Owned;
	endif;
        
      case Fwd_GetS:
        msg_processed := false;
        
      case Fwd_GetM:
        msg_processed := false;
      
      case Inv_Ack:
        pan := pan - 1; 
        
        
      else
        ErrorUnhandledMsg(msg, p);
        
    endswitch;

  case OM_A_WaitForGetMAck:
    switch msg.mtype
      case Fwd_GetS:
	Send(OwnedData, msg.src, p, VC4, pv, 0);
	--fan:=fan+1;

      case Fwd_GetM:
	  Send(OwnedData, msg.src, p, VC4, pv, msg.sharenum);
	  ps := IM_AD;

      case GetM_Ack:
	if (msg.sharenum=0)
	then
	  ps :=P_Modified;
	  Send(Fwd_Ack, HomeType, p, VC7, UNDEFINED,0);
	else
	  pan := msg.sharenum; 
	endif;
      case Inv_Ack:
	if (pan=0)
	then
	  msg_processed := false;
	endif;
	if (pan=1)
	then
	  pan :=0;
	  ps := P_Modified;
	  Send(Fwd_Ack, HomeType, p, VC7, UNDEFINED,0);
	endif;
	if (pan>1)
	then
	  pan:=pan-1;
	endif;
	
    endswitch;

  case IM_AD_WaitForGetMAck:
    switch msg.mtype
      case GetM_Ack:
	if (msg.sharenum=0)
	then
	  ps :=IM_AD;
	  undefine pv;
	else
	  pan := msg.sharenum; 
	endif;
	--msg_processed := false;
      case Data:
	msg_processed := false;
    endswitch;


  case OM_A:	--wait for GetMAck and FwdAck
    switch msg.mtype
      case Fwd_GetS:
	Send(FwdData, msg.src, p, VC4, pv, 0);
	fan:=fan+1;
      case Fwd_GetM:
	if (msg.sharenum=0)
	then
	  Send(FwdData, msg.src, p, VC4, pv, 0);
	  ps:=OM_A;
	endif;	
    endswitch;
  
  case SM_AD:
    switch msg.mtype
      case Fwd_GetS:
        msg_processed := false;
        
      case Fwd_GetM:
        msg_processed := false;
        
      case Invalidation:
        Send(Inv_Ack, msg.src, p, VC5, UNDEFINED, 0);
        Send(Inv_Ack, HomeType, p, VC5, UNDEFINED, 0);
        ps := IM_AD;
        
      case Data:
        
        if (msg.src = HomeType)
        then 
          if (msg.sharenum = 0)
          then
            ps := P_Modified;
            pv := msg.val;
            Send(Inv_Ack, HomeType, p, VC5, UNDEFINED, 0);
          endif;
          
          if (msg.sharenum > 0)
          then
            ps := SM_A;
            pan:= msg.sharenum - 1;
            pv := msg.val;
            Send(Inv_Ack, HomeType, p, VC5, UNDEFINED, 0);
          endif;

          if !(msg.src = HomeType)
          then
            ps := P_Modified;
            pv := msg.val;
          endif;
        endif;

      case FwdData:
	if (msg.sharenum=0)
	then
	  ps := P_Modified;
	  pv := msg.val;
	  Send(Fwd_Ack, HomeType, p, VC7, UNDEFINED, 0);
	endif;
	if (msg.sharenum>0)
	then
	  ps:= SM_A;
	  pan:=msg.sharenum;
	  pv:=msg.val;
	  Send(Fwd_Ack, HomeType, p, VC7, UNDEFINED,0);
	  Send(Fwd_Ack, msg.src, p, VC7, UNDEFINED, 0);
	endif;
	
        
      case OwnedData:
	if (msg.sharenum>0)
	then
	  pan:=msg.sharenum;
	  Send(Fwd_Ack, HomeType, p, VC7, UNDEFINED, 0);
	  pv :=msg.val;
	  ps :=IM_A;
	else
	  pv :=msg.val;
	  ps :=P_Modified;
	  Send(Fwd_Ack, HomeType, p, VC7, UNDEFINED, 0);
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
        if (fan<ProcCount)
	then
          Send(FwdData, msg.src, p, VC4, pv, 0);
	  fan:=fan+1;
          ps := OI_A;
	else
	  msg_processed:=false;
	endif;
        
      case Fwd_GetM:
        Send(Data, msg.src, p, VC4, pv, msg.sharenum);
        Send(Fwd_Ack, HomeType, p, VC7, UNDEFINED, 0);
        ps := II_A;
        
      case Put_Ack:
        ps := P_Invalid;
        undefine pv;

      case Fwd_Ack:

      else
        ErrorUnhandledMsg(msg, p);
        
    endswitch;

  case EI_A:
    switch msg.mtype
      case Fwd_GetS:
	if (fan<ProcCount)
	then
          Send(FwdData, msg.src, p, VC4, pv, 0);
          fan:= fan+1;
          ps := OI_A;
	else
	  msg_processed:=false;
	endif;
      
      case Fwd_GetM:
        Send(Data, msg.src, p, VC4, pv, msg.sharenum);
        Send(Fwd_Ack, HomeType, p, VC7, UNDEFINED, 0);
        ps := II_A;
      
      case Put_Ack:
	ps:=P_Invalid;
	undefine pv;

      case Put_Ack_S:
	msg_processed:=false;

      case Fwd_Ack:
	fan:=fan-1;
      
      else
        ErrorUnhandledMsg(msg, p);
        
    endswitch;  
      
    
  case SI_A:
    switch msg.mtype
      case Invalidation:
        Send(Inv_Ack, msg.src, p, VC5, UNDEFINED, 0);
        Send(Inv_Ack, HomeType, p, VC5, UNDEFINED, 0);
        ps := II_A;
      
      case Put_Ack:
        ps := P_Invalid;
        undefine pv;
      
      else
        ErrorUnhandledMsg(msg, p);
        
    endswitch;  

  case OI_A_WaitForPutAck: --EI_A/MI_A + Fwd_GetM
    switch msg.mtype
      case Fwd_GetS:
	if (fan<ProcCount)
	then
	  Send(FwdData, msg.src, p, VC4, pv, 0);
	  ps := OI_A;
          fan := fan+1;
	else
	  msg_processed := false;
	endif;

      case Fwd_GetM:
	Send(FwdData, msg.src, p, VC4, pv, msg.sharenum);
	fan:= 1;
	ps := OI_A;

      case Put_Ack:
	  if (pan=0)
	  then
            ps := P_Invalid;
            undefine pv;
	  else
	    msg_processed := false;
	  endif;

      case Inv_Ack:
	if (pan>1)
        then
	  pan := pan-1;
        endif;
	if (pan=1)
	then
	  --ps := P_Invalid;
	  --undefine pv;
	  pan := 0;
	endif;

      case Put_Ack_S:
	
	if (pan=0)
	then
            pan := msg.sharenum;
	else
	    msg_processed := false;
	endif;

      case Fwd_Ack:
	ps:= II_A;
	--undefine pv;

      else
        ErrorUnhandledMsg(msg, p);
    endswitch;  

    case OI_A_WaitForFwdAck:     --O + GetM
    switch msg.mtype
      case Fwd_GetS:
	if (fan<ProcCount)
	then
	  Send(FwdData, msg.src, p, VC4, pv, 0);
          fan:= fan+1;
	else
	  msg_processed := false;
	endif;

      case Fwd_GetM:
	Send(FwdData, msg.src, p, VC4, pv, msg.sharenum);
	fan:=1;

      case Put_Ack:
          ps := P_Invalid;
          undefine pv;

      case Inv_Ack:
	if (pan=1)
	then
	  --ps := P_Invalid;
	  --undefine pv;
	  pan := 0;
	endif;
	if (pan>1)
        then
	  pan := pan-1;
        endif;
	

      case Put_Ack_S:
	pan := msg.sharenum;

      case Fwd_Ack:
	
	if (pan=0)
	then
	  fan:=fan-1;
	  if (fan=0)
	  then
	    ps:= P_Invalid;
	  endif;
	else
	  msg_processed := false;
	endif;
	
	--undefine pv;

      else
        ErrorUnhandledMsg(msg, p);
    endswitch;  

  case OI_A: --wait for both Put_Ack and Fwd_Ack
  switch msg.mtype
      case Fwd_GetS:
	if (fan<ProcCount)
	then
	  Send(FwdData, msg.src, p, VC4, pv, 0);
	  fan:=fan+1;
	else
	  msg_processed := false;
	endif;

      case Fwd_GetM:
	if (fan=0)
	then
	  Send(FwdData, msg.src, p, VC4, pv, msg.sharenum);
	  fan:=1
	else
	  msg_processed := false;
	endif;

      case Put_Ack:
          ps := OI_A_WaitForFwdAck;
          undefine pv;

      case Inv_Ack:
	if (pan>1)
        then
	  pan := pan-1;
        endif;
	if (pan=1)
	then
	  --ps := P_Invalid;
	  --undefine pv;
	  pan := 0;
	endif;

      case Put_Ack_S:
	pan := msg.sharenum;
	ps:= OI_A_WaitForFwdAck;
	undefine pv;

      case Fwd_Ack:
	fan:=fan-1;
	if (fan=0)
	then
	  ps:= OI_A_WaitForPutAck;
	endif;
	--undefine pv;

      else
        ErrorUnhandledMsg(msg, p);
    endswitch;  


    
  case II_A:
    switch msg.mtype
      case Put_Ack:
        ps := P_Invalid;
        undefine pv;

      case Put_Ack_S:
	ps :=P_Invalid;
	undefine pv;
      --case Inv_Ack:

      case Fwd_GetS:
      case Fwd_Ack:
        
    else
        ErrorUnhandledMsg(msg, p);
        
    endswitch;   
  endswitch;

  endalias;
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
 	    
 	    if (p.state = P_Exclusive)
 	    then
 	      p.val := v;
 	      LastWrite := v;
 	      p.state := P_Modified;
 	    endif;
          endrule;
	endruleset;
	
	rule "write request"
	  if (p.state = P_Invalid)
          then
            Send(GetM, HomeType, n, VC8, UNDEFINED, 0);
 	    p.state := IM_AD;  
 	  endif;
	  if (p.state = P_Exclusive)
	  then
	    p.state := P_Modified;
	  endif;
 	  if (p.state = P_Shared)
 	  then
 	    Send(GetM, HomeType, n, VC8, UNDEFINED, 0);
 	    p.state := SM_AD;  
 	  endif;
	  if (p.state = P_Owned)
	  then
	    p.state:= OM_A_WaitForGetMAck;
	    Send(GetM, HomeType, n, VC8, UNDEFINED, 0);
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
        Send(PutS, HomeType, n, VC6, UNDEFINED, 0);
        p.state := SI_A;
      endif;
      if (p.state = P_Modified)
      then
        Send(PutM, HomeType, n, VC6, p.val, 0);
        p.state := MI_A;
      endif;
      if (p.state = P_Exclusive)
      then
        Send(PutE, HomeType, n, VC6, UNDEFINED, 0);
        p.state := EI_A;
      endif;
      if (p.state = P_Owned)
      then
        Send(PutO, HomeType, n, VC6, p.val, 0);
        p.state := OI_A;
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
    Procs[i].InvAckNum := 0;
    Procs[i].FwdAckNum := 0;
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

-- for MESI
invariant "Exclusive implies empty sharers list"
  HomeNode.state = H_Exclusive
    ->
      MultiSetCount(i:HomeNode.sharers, true) = 0;

invariant "the value of Processor in exclusive state should be the same as Memory"
  Forall n : Proc Do
     Procs[n].state = P_Exclusive
    ->
     Procs[n].val = HomeNode.val
  end;
