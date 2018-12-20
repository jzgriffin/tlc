Require Import Coq.Lists.List.
Require Import Coq.Arith.EqNat.
Require Import Coq.Arith.Minus.
Require Import Coq.Arith.Plus.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.Vectors.Vector.
Require Import TLC.Byte.
Require Import TLC.Component.
Require Import TLC.FairLossLink.
Require Import TLC.ProgramLogic.
Require Import TLC.Queue.
Require Import TLC.SequentLogic.
Require Import TLC.Stack.
Require Import TLC.TemporalLogic.
Require Import TLC.Term.
Require Import TLC.TupleMap.
Require Import TLC.Variant.
Require Import TLC.Word.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Primitives *)
Definition ip_address := word 128.
Definition ip_version := word 4.
Definition ip_traffic_class := byte.
Definition ip_flow_label := word 20.
Definition ip_length := word 16.
Definition ip_hop_limit := byte.
Definition ip_payload := bytes.

(* Constants *)
Definition ip_version_6 : ip_version := $6.

(* Structures *)
Inductive ip_next_header :=
| IpNextHeaderTcp.

Record ip_header :=
  IpHeader {
    ip_header_version : ip_version;
    ip_header_traffic_class : ip_traffic_class;
    ip_header_flow_label : ip_flow_label;
    ip_header_payload_length : ip_length;
    ip_header_next_header : ip_next_header;
    ip_header_hop_limit : ip_hop_limit;
    ip_header_src_address : ip_address;
    ip_header_dst_address : ip_address;
  }.

Record ip_datagram :=
  IpDatagram {
    ip_datagram_header : ip_header;
    ip_datagram_payload : ip_payload;
  }.

(* Encoders/decoders *)
Definition ip_next_header_to_word (nh : ip_next_header) : byte :=
  $match nh with
  | IpNextHeaderTcp => 6
  end.

Definition word_to_ip_next_header (w : byte) : option ip_next_header :=
  if weqb w $6 then Some IpNextHeaderTcp
  else None.

Definition ip_header_to_bytes (h : ip_header) : bytes :=
  word64_to_bytes (
    ip_header_version h ^::
    ip_header_traffic_class h ^::
    ip_header_flow_label h ^::
    ip_header_payload_length h ^::
    ip_next_header_to_word (ip_header_next_header h) ^::
    ip_header_hop_limit h) ++
  word128_to_bytes (ip_header_src_address h) ++
  word128_to_bytes (ip_header_dst_address h).

Definition bytes_to_ip_header (bs : bytes) : option (ip_header * bytes) :=
  match bytes_to_word32s bs with
  | v_tc_fl :: pl_nh_hl ::
    sa1 :: sa2 :: sa3 :: sa4 ::
    da1 :: da2 :: da3 :: da4 :: ws' =>
    let v := split1 4 _ v_tc_fl in
    let tc_fl := split2 4 _ v_tc_fl in
    let tc := split1 8 _ tc_fl in
    let fl := split2 8 _ tc_fl in
    let pl := split1 16 _ pl_nh_hl in
    let nh_hl := split2 16 _ pl_nh_hl in
    let nh' := split1 8 _ nh_hl in
    let hl := split2 8 _ nh_hl in
    let sa := (sa1 ^:: sa2 ^:: sa3 ^:: sa4)%word in
    let da := (da1 ^:: da2 ^:: da3 ^:: da4)%word in
    match word_to_ip_next_header nh' with
    | Some nh =>
      Some (IpHeader v tc fl pl nh hl sa da, word32s_to_bytes ws')
    | None => None
    end
  | _ => None
  end.

Definition ip_datagram_to_bytes (d : ip_datagram) : bytes :=
  ip_header_to_bytes (ip_datagram_header d) ++ (ip_datagram_payload d).

Definition bytes_to_ip_datagram (bs : bytes) : option ip_datagram :=
  match bytes_to_ip_header bs with
  | Some (h, p) =>
    if weqb $(length p) (ip_header_payload_length h) then Some (IpDatagram h p)
    else None
  | None => None
  end.

(* Component *)
Definition ip_node := ip_address.
Definition ip_message := bytes.

Inductive ip_request :=
| Send_ip
  (tc : ip_traffic_class) (fl : ip_flow_label)
  (nh : ip_next_header) (hl : ip_hop_limit)
  (sa da : ip_address) (p : ip_payload).

Inductive ip_indication :=
| Receive_ip (d : ip_datagram).

Section sub_interfaces.

  Import VectorNotations.

  Definition request_fl_ip : Type := request_fl ip_node ip_message.
  Definition indication_fl_ip : Type := indication_fl ip_node ip_message.

  Definition ip_sub_interfaces : interfaces :=
    existT _ _ [(request_fl_ip, indication_fl_ip)].

End sub_interfaces.

Definition ip_state := unit.

Definition ip :=
  let initialize n := tt in
  let request n s ir :=
    match ir with
    | Send_ip tc fl nh hl sa da p =>
      let h := IpHeader ip_version_6 tc fl $(length p) nh hl sa da in
      let d := IpDatagram h p in
      let s' := s in
      let ors := [Send_fl da (ip_datagram_to_bytes d)] in
      let ois := [] in
      (s', ors, ois)
    end in
  let indication n' s ii :=
    match ii with
    | Deliver_fl n m =>
      match bytes_to_ip_datagram m with
      | Some d =>
        let s' := s in
        let ors := [] in
        let ois :=
          if weqb n' (ip_header_dst_address (ip_datagram_header d)) then
            [Receive_ip d]
          else [] in
        (s', ors, ois)
      | None =>
        let s' := s in
        let ors := [] in
        let ois := [] in
        (s', ors, ois)
      end
    end in
  let periodic n s :=
    let s' := s in
    let ors := [] in
    let ois := [] in
    (s', ors, ois) in
  @Component ip_node ip_message ip_request ip_indication
    ip_sub_interfaces ip_state
    initialize request indication periodic.

Definition ip_stack : stack ip_node ip_message (ir_event ip) (oi_event ip).
Proof.
  apply ComponentStack, TupleMapCons; [apply FairLossLink | apply TupleMapNil].
Defined.

Lemma ip_ir_term (x : term ip ip_request) : term ip (ir_event ip).
Proof. assumption. Qed.
Lemma ip_oi_term (x : term ip ip_indication) : term ip (oi_event ip).
Proof. assumption. Qed.

Theorem IP_1 (n n' : term ip ip_node) (d : term ip ip_datagram) : [] |- ip, (
  let h := (^ip_datagram_header <- d)%tlc in
  let fl := (^ip_header_flow_label <- h)%tlc in
  let nh := (^ip_header_next_header <- h)%tlc in
  let sa := (^ip_header_src_address <- h)%tlc in
  let p := (^ip_datagram_payload <- d)%tlc in
  (on: n, when[]<-: ip_oi_term (^Receive_ip <- d)) <~
  (exists: tc, exists: hl,
    on: n', when[]->: ip_ir_term
      (^Send_ip <- ^tc <- fl <- nh <- ^hl <- sa <- n <- p))
).
Proof.
Admitted. (* TODO *)
