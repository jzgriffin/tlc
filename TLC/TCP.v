Require Import Coq.FSets.FMapAVL.
Require Import Coq.Lists.List.
Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.Vectors.Vector.
Require Import TLC.Byte.
Require Import TLC.Component.
Require Import TLC.IP.
Require Import TLC.Stack.
Require Import TLC.TupleMap.
Require Import TLC.Word.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition tcp_payload := bytes.
Definition tcp_port := word 16.
Definition tcp_number := word 32.
Definition tcp_offset := word 4.
Definition tcp_window := word 16.
Definition tcp_checksum := word 16.
Definition tcp_pointer := word 16.
Definition tcp_mss := word 16.

Record tcp_control :=
  TcpControl {
    tcp_control_urg : bool;
    tcp_control_ack : bool;
    tcp_control_psh : bool;
    tcp_control_rst : bool;
    tcp_control_syn : bool;
    tcp_control_fin : bool;
  }.

Inductive tcp_option :=
| TcpOptionEnd
| TcpOptionNone
| TcpOptionMss (mss : tcp_mss).
Definition tcp_options := list tcp_option.

Record tcp_header :=
  TcpHeader {
    tcp_header_src_port : tcp_port;
    tcp_header_dst_port : tcp_port;
    tcp_header_seq_num : tcp_number;
    tcp_header_ack_num : tcp_number;
    tcp_header_offset : tcp_offset;
    tcp_header_control : tcp_control;
    tcp_header_window : tcp_window;
    tcp_header_urgent_ptr : tcp_pointer;
    tcp_header_options : tcp_options;
  }.

Record tcp_segment :=
  TcpSegment {
    tcp_segment_header : tcp_header;
    tcp_segment_payload : tcp_payload;
  }.

Record tcp_socket :=
  TcpSocket {
    tcp_socket_address : ip_address;
    tcp_socket_port : tcp_port;
  }.

(* Component *)
Definition tcp_node := ip_address.
Definition tcp_message := bytes.

Definition tcp_connection := nat.
Module TcpConnectionMap := FMapAVL.Make(Nat_as_OT).

(* From RFC 791 page 51 *)
Definition tcp_ip_traffic_class : ip_traffic_class := $0.
Definition tcp_ip_flow_label : ip_flow_label := $0.
Definition tcp_ip_next_header : ip_next_header := IpNextHeaderTcp.
Definition tcp_ip_hop_limit : ip_hop_limit := $60.

Inductive tcp_open_mode :=
| Active_tcp
| Passive_tcp.

Inductive tcp_request :=
| Open_tcp
  (p : tcp_port) (fs : option tcp_socket) (om : tcp_open_mode)
| Close_tcp (c : tcp_connection)
| Send_tcp (c : tcp_connection) (p : tcp_payload)
| Receive_tcp (c : tcp_connection)
| Abort_tcp (c : tcp_connection).

Inductive tcp_indication :=
| OpenSuccess_tcp (p : tcp_port) (fs : option tcp_socket) (om : tcp_open_mode)
  (c : tcp_connection)
| OpenFailure_tcp (p : tcp_port) (fs : option tcp_socket) (om : tcp_open_mode)
| CloseSuccess_tcp (c : tcp_connection)
| CloseFailure_tcp (c : tcp_connection)
| SendSuccess_tcp (c : tcp_connection) (p : tcp_payload)
| SendFailure_tcp (c : tcp_connection) (p : tcp_payload)
| ReceiveSuccess_tcp (c : tcp_connection) (s : tcp_segment)
| ReceiveFailure_tcp (c : tcp_connection)
| AbortSuccess_tcp (c : tcp_connection)
| AbortFailure_tcp (c : tcp_connection).

Section sub_interfaces.

  Import VectorNotations.

  Definition tcp_sub_interfaces : interfaces :=
    let ip_ir : Type := ip_request in
    let ip_oi : Type := ip_indication in
    existT _ _ [(ip_ir, ip_oi)].

End sub_interfaces.

Record tcb :=
  Tcb {
  }.

Definition tcp_state := TcpConnectionMap.t tcb.

Definition tcp :=
  let initialize n := TcpConnectionMap.empty tcb in
  let request n s ir :=
    match ir with
    | Open_tcp p fs om =>
      (* TODO *)
      let s' := s in
      let ors := [] in
      let ois := [] in
      (s', ors, ois)
    | Close_tcp c =>
      (* TODO *)
      let s' := s in
      let ors := [] in
      let ois := [] in
      (s', ors, ois)
    | Send_tcp c p =>
      (* TODO *)
      let s' := s in
      let ors := [] in
      let ois := [] in
      (s', ors, ois)
    | Receive_tcp c =>
      (* TODO *)
      let s' := s in
      let ors := [] in
      let ois := [] in
      (s', ors, ois)
    | Abort_tcp c =>
      (* TODO *)
      let s' := s in
      let ors := [] in
      let ois := [] in
      (s', ors, ois)
    end in
  let indication n' s ii :=
    (* TODO *)
    let s' := s in
    let ors := [] in
    let ois := [] in
    (s', ors, ois) in
  let periodic n s :=
    (* TODO *)
    let s' := s in
    let ors := [] in
    let ois := [] in
    (s', ors, ois) in
  @Component tcp_node tcp_message tcp_request tcp_indication
    tcp_sub_interfaces tcp_state
    initialize request indication periodic.

Definition tcp_stack :
  stack tcp_node tcp_message (ir_event tcp) (oi_event tcp).
Proof.
  apply ComponentStack, TupleMapCons; [apply ip_stack | apply TupleMapNil].
Defined.
