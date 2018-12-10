Require Import TLC.Byte.
Require Import TLC.Component.
Require Import TLC.IP.
Require Import TLC.Word.
Require Import Coq.FSets.FMapAVL.
Require Import Coq.Lists.List.
Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.Vectors.Vector.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition tcp_data := bytes.
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
| TcpOptionMSS (mss : tcp_mss).
Definition tcp_options := list tcp_option.

Record tcp_header :=
  TcpHeader {
    tcp_header_src_port : tcp_port;
    tcp_header_dst_port : tcp_port;
    tcp_header_seq_num : tcp_number;
    tcp_header_ack_num : tcp_number;
    tcp_header_data_offset : tcp_offset;
    tcp_header_control : tcp_control;
    tcp_header_window : tcp_window;
    tcp_header_checksum : tcp_checksum;
    tcp_header_urgent_ptr : tcp_pointer;
    tcp_header_options : tcp_options;
  }.

Record tcp_segment :=
  TcpSegment {
    tcp_segment_header : tcp_header;
    tcp_segment_data : tcp_data;
  }.

Record tcp_socket :=
  TcpSocket {
    tcp_socket_address : ip_address;
    tcp_socket_port : tcp_port;
  }.

Definition tcp_node := ip_address.
Definition tcp_message := tcp_data.

Definition tcp_connection := nat.
Module TcpConnectionMap := FMapAVL.Make(Nat_as_OT).

(* From RFC 791 page 51 *)
Definition tcp_ip_ttl : ip_time_to_live := natToWord _ 60.
Definition tcp_ip_service_type :=
  IpServiceType
    IpPrecedenceRoutine
    IpDelayNormal
    IpThroughputNormal
    IpReliabilityNormal.
(* From RFC 790 page 6 *)
Definition tcp_ip_protocol : ip_protocol := natToWord _ 6.

Inductive tcp_open_mode : Type :=
| Active_tcp
| Passive_tcp.

Inductive tcp_request : Type :=
| Open_tcp :
  tcp_node -> tcp_port -> option tcp_socket -> tcp_open_mode ->
  tcp_request
| Close_tcp :
  tcp_node -> tcp_connection ->
  tcp_request
| Send_tcp :
  tcp_node -> tcp_connection -> tcp_message ->
  tcp_request
| Receive_tcp :
  tcp_node -> tcp_connection ->
  tcp_request
| Abort_tcp :
  tcp_node -> tcp_connection ->
  tcp_request.

Inductive tcp_indication : Type :=
| OpenSuccess_tcp :
  tcp_node -> tcp_port -> option tcp_socket -> tcp_open_mode ->
  tcp_connection -> tcp_indication
| OpenFailure_tcp :
  tcp_node -> tcp_port -> option tcp_socket -> tcp_open_mode ->
  tcp_indication
| CloseSuccess_tcp :
  tcp_node -> tcp_connection ->
  tcp_indication
| CloseFailure_tcp :
  tcp_node -> tcp_connection ->
  tcp_indication
| SendSuccess_tcp :
  tcp_node -> tcp_connection -> tcp_message ->
  tcp_indication
| SendFailure_tcp :
  tcp_node -> tcp_connection -> tcp_message ->
  tcp_indication
| ReceiveSuccess_tcp :
  tcp_node -> tcp_connection ->
  tcp_message -> tcp_indication
| ReceiveFailure_tcp :
  tcp_node -> tcp_connection ->
  tcp_indication
| AbortSuccess_tcp :
  tcp_node -> tcp_connection ->
  tcp_indication
| AbortFailure_tcp :
  tcp_node -> tcp_connection ->
  tcp_indication.

Section sub_interfaces.

  Import VectorNotations.

  Definition tcp_sub_interfaces : interfaces :=
      existT _ _ [].

End sub_interfaces.

Record tcb :=
  Tcb {
  }.

Definition tcp_state := TcpConnectionMap.t tcb.

Definition tcp :=
  let initialize n := TcpConnectionMap.empty tcb in
  let request n s ir :=
    match ir with
    | Open_tcp n' p k m =>
      (* TODO *)
      let s' := s in
      let ors := [] in
      let ois := [] in
      (s', ors, ois)
    | Close_tcp n' c =>
      (* TODO *)
      let s' := s in
      let ors := [] in
      let ois := [] in
      (s', ors, ois)
    | Send_tcp n' c m =>
      (* TODO *)
      let s' := s in
      let ors := [] in
      let ois := [] in
      (s', ors, ois)
    | Receive_tcp n' c =>
      (* TODO *)
      let s' := s in
      let ors := [] in
      let ois := [] in
      (s', ors, ois)
    | Abort_tcp n' c =>
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
