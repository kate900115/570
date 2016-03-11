
-- Three-state 3-hop MSI protocol

----------------------------------------------------------------------
-- Constants
----------------------------------------------------------------------
const
  ProcCount: 3;          -- number processors
  ValueCount:   2;       -- number of data values.
  VC0: 0;                -- low priority
  VC1: 1;
  QMax: 2;
  NumVCs: VC1 - VC0 + 1;
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

  MessageType: enum {  GetS,            -- request for data
                       GetM,            -- request for data, and will modified that data.
                       
                       Fwd_GetS,		-- the home node is not the owner, instead other Proc is the owner
                       Fwd_GetM,
                       
                       Invidation,		
                                             
					   PutS,            -- writeback the data in share state.
					   PutM,            -- writeback the data in modified state.
                           
                       Get_Ack,
                       Put_Ack,			-- respond from home node to indicate the value is successful writeback    
                       Inv_Ack 		    -- respond from other proc to indicate the block is invalidated
                    };

  Message:
    Record
      mtype: MessageType;
      src: Node;
      -- do not need a destination for verification; the destination is indicated by which array entry in the Net the message is placed
      
      vc: VCType;
      val: Value;
      -- indicate the index of nodes in the sharer's state
      
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
      state: enum { P_Valid, P_Invalid, 								--stable states
                  IS_D, IM_AD, IM_A, SM_AD, MI_A, SI_A, II_A			--transient states
                  };
      val: Value;
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
         );
var msg:Message;
Begin
  Assert (MultiSetCount(i:Net[dst], true) < NetMax) "Too many messages";
  msg.mtype := mtype;
  msg.src   := src;
  msg.vc    := vc;
  msg.val   := val;
  msg.sharelist := slist;
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



-- Sends a message to all sharers except rqst
Procedure SendInvReqToSharers(rqst:Node);
Begin
  for n:Node do
    if (IsMember(n, Proc) &
        MultiSetCount(i:HomeNode.sharers, HomeNode.sharers[i] = n) != 0)
    then
      if n != rqst
      then 
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
      Send(Get_Ack, msg.src, HomeType, VC1, HomeNode.val);
      
    case GetM:
	  HomeNode.state := H_Modified;
      HomeNode.owner := msg.src;
      Send(Get_Ack, msg.src, HomeType, VC1, HomeNode.val);
      SendInvReqToSharers(msg.src);
    else
      ErrorUnhandledMsg(msg, HomeType);

    endswitch;

  case H_Shared:							
  --H_Valid means that there is other node who has the value.
  --That node should return the value to the requesting node.
    Assert (cnt = 0) 
       "HomeNode has no owner, but line is Valid";

    switch msg.mtype
    case GetS:     
      Send(Get_Ack, msg.src, HomeType, VC1, HomeNode.val);
      AddToSharersList(msg.src);
            
    case GetM:
      assert (msg.src = HomeNode.owner) "Writeback from non-owner";
      HomeNode.state := HT_Pending;
      Send(Get_Ack, msg.src, HomeType, VC1, HomeNode.val);
      Send(Invalidation, msg.src, HomeType, VC1, UNDEFINED);
      undefine HomeNode.owner
      
    case PutM:
      assert (msg.src = HomeNode.owner) "Writeback from non-owner";

    else
      ErrorUnhandledMsg(msg, HomeType);

    endswitch;

  case HT_Pending:
    switch msg.mtype
   
    case WBReq:
    
    -- When the home directory is in the transient state, 
    -- it means that it is waiting for the data from the owner
    -- if it receive a WBReq, it means the data from the old owner send back date to the home node
    -- So it will send this data to the requestor
    
      Assert (!IsUnDefined(HomeNode.owner)) "owner undefined";
      HomeNode.state := H_Valid;
      HomeNode.val := msg.val;
      Send(ReadAck, HomeNode.owner, HomeType, VC1, HomeNode.val);

    case ReadReq:
    
    -- When there is another read request, it will put the read request into inbox
    
    	msg_processed := false; -- stall message in InBox

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

  switch ps
  case P_Valid:

    switch msg.mtype
    case RecallReq:
      Send(WBReq, msg.src, p, VC1, pv);
      Undefine pv;
      ps := P_Invalid;
    else
      ErrorUnhandledMsg(msg, p);
    endswitch;

  case PT_Pending:

    switch msg.mtype
    case ReadAck:
      pv := msg.val;
      ps := P_Valid;
    case RecallReq:
    	msg_processed := false; -- stall message in InBox
    else
      ErrorUnhandledMsg(msg, p);
    endswitch;


  case PT_WritebackPending:    

    switch msg.mtype
    case WBAck:
      ps := P_Invalid;
      undefine pv;
    case RecallReq:				-- treat a recall request as a Writeback acknowledgement
      ps := P_Invalid;
      undefine pv;
    else
      ErrorUnhandledMsg(msg, p);
		endswitch;

  ----------------------------
  -- Error catch
  ----------------------------
  else
    ErrorUnhandledState();

  endswitch;
  
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
   	 (p.state = P_Valid)
    	==>
 		   p.val := v;      
 		   LastWrite := v;  --We use LastWrite to sanity check that reads receive the value of the last write
  	endrule;
	endruleset;

  rule "read request"
    p.state = P_Invalid 
  ==>
    Send(ReadReq, HomeType, n, VC0, UNDEFINED);
    p.state := PT_Pending;
  endrule;


  rule "writeback"
    (p.state = P_Valid)
  ==>
    Send(WBReq, HomeType, n, VC1, p.val); 
    p.state := PT_WritebackPending;
    undefine p.val;
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
  HomeNode.val := v;
	endfor;
	LastWrite := HomeNode.val;
  
  -- processor initialization
  for i:Proc do
    Procs[i].state := P_Invalid;
    undefine Procs[i].val;
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

invariant "values in valid state match last write"
  Forall n : Proc Do	
     Procs[n].state = P_Valid
    ->
			Procs[n].val = LastWrite --LastWrite is updated whenever a new value is created 
	end;
	
invariant "value is undefined while invalid"
  Forall n : Proc Do	
     Procs[n].state = P_Invalid
    ->
			IsUndefined(Procs[n].val)
	end;
	
/*	
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
*/	
