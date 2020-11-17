(** @author  
    Christopher Janas (cjj36),
    Kartikay Jain (kj295) *)

(** [index c] is the 0-based index of [c] in the alphabet.
    Requires: [c] is an uppercase letter in A..Z. *)

let index (c:char) : int =
  (Char.code c) - 65

(** [index_inverse x] is the character s.t. (index (index_inverse x) = x)
    Requires: [x] is an integer in 0..25. *)

let index_inverse (x:int) =
  Char.chr (x+65)

(** [mod_pos x y] is the value of x mod y that is between 0..y-1. 
    If x is negative, the negative value of x mod y wraps around to a positive
    integer. *)

let mod_pos x y = 
  (x mod y) + (if (x >= 0) then 0 else y)

(** [mod_pos_26 x] is the value of mod_pos x 26. *)

let mod_pos_26 x = 
  mod_pos x 26

(** [map_r_to_l wiring top_letter input_pos] is the left-hand output position
    at which current would appear when current enters at right-hand input
    position [input_pos] to a rotor whose wiring specification is given by
    [wiring].  The orientation of the rotor is given by [top_letter], 
    which is the top letter appearing to the operator in the rotor's 
    present orientation.
    Requires: 
    	[wiring] is a valid wiring specification, 
    	[top_letter] is in A..Z, and 
    	[input_pos] is in 0..25. *)

let map_r_to_l (wiring:string) (top_letter:char) (input_pos:int) : int =
  (* Current flows to the contact that is input_pos + offset (mod 26) *)
  (input_pos + index top_letter) mod 26
  (* Current flows from right hand contact to left-hand contact based on
        the wiring. *)
  |> String.get wiring 
  |> index 
  (* Current flows from left-hand contact to the position that is
      (left-hand contact) - offset (mod 26). *)
  |> (fun x -> x - index top_letter)
  |> mod_pos_26

(** [map_l_to_r] computes the same function as [map_r_to_l], except 
    for current flowing left to right. *)

let map_l_to_r (wiring:string) (top_letter:char) (input_pos:int) : int =
  (* Current flows to the contact that is input_pos + offset (mod 26) *)
  (input_pos + index top_letter) mod 26
  (* Current flows from left hand contact to right-hand contact based on
      the wiring. *)
  |> index_inverse
  |> String.index wiring
  (* Current flows from right-hand contact to the position that is
      (right-hand contact) - offset (mod 26). *)
  |> (fun x -> x - index top_letter)
  |> mod_pos_26

(** [map_refl wiring input_pos] is the output position at which current would 
    appear when current enters at input position [input_pos] to a reflector 
    whose wiring specification is given by [wiring].
    Requires: 
    	[wiring] is a valid reflector specification, and 
      [input_pos] is in 0..25. *)

let map_refl (wiring:string) (input_pos:int) : int =
  map_r_to_l wiring 'A' input_pos

(** [map_plug plugs c] is the letter to which [c] is transformed
    by the plugboard [plugs].
    Requires:
      [plugs] is a valid plugboard, and
      [c] is in A..Z. *)

let rec map_plug (plugs:(char*char) list) (c:char) =
  match plugs with
  | [] -> c
  | h :: t -> 
    if (fst h) = c then snd h 
    else if (snd h) = c then fst h 
    else map_plug t c

(* [rotor] represents an Enigma rotor. *)

type rotor = {
  wiring : string;
  turnover : char;
}

(* [oriented_rotor] represents a rotor that is installed on the spindle hence 
    has a top letter. *)

type oriented_rotor = {
  rotor : rotor;
  top_letter : char;
}

(* [config] represents the configuration of an Enigma machine. 
    See the assignment handout for a description of the fields. *)

type config = {
  refl : string;
  rotors : oriented_rotor list;
  plugboard : (char*char) list;
}

(** [map_rotors_rl_lr f orl input] computes 
    the output position that results when 
    current enters and passes through an entire list [orl] of rotors 
    at input position int [input]
    either from left to right or right to left 
    depending on the function [f] *)

let rec map_rotors_rl_lr f orl input = 
  match orl with 
  | [] -> input
  | h :: t -> 
    map_rotors_rl_lr f t (f h.rotor.wiring h.top_letter input)

(** [map_rotors_r_to_l] computes the output position that results when 
    current enters and passes through an entire list [orl] of rotors 
    at input position int [input] *)

let  map_rotors_r_to_l = 
  map_rotors_rl_lr map_r_to_l

(** [map_rotors_l_to_r] computes the output position that results when 
    current enters and passes through an entire list [orl] of rotors 
    at input position int [input] *)

let  map_rotors_l_to_r = 
  map_rotors_rl_lr map_l_to_r

(** [cipher_char config c] is the letter to which the Enigma machine 
    ciphers input [c] when it is in configuration [config].
    Requires:
      [config] is a valid configuration, and
      [c] is in A..Z. *)

let cipher_char (config:config) (c:char) : char =
  c 
  |> map_plug config.plugboard 
  |> index 
  |> map_rotors_r_to_l (List.rev config.rotors)
  |> map_refl config.refl 
  |> map_rotors_l_to_r config.rotors
  |> index_inverse 
  |> map_plug config.plugboard

(** [step_rotor r] returns the rotor with top_letter of [r] advanced by
    1 letter. *)

let step_rotor r = 
  { rotor = r.rotor; 
    top_letter = (r.top_letter |> index |> (+) 1 
                  |> mod_pos_26 |> index_inverse)} 

(** [stepcheck_topletter original total] at the end of the recursive call
    returns the total list of rotors, in reverse order, with each rotor
    being stepped according to the following rules:
    Rule 1: Just before each letter is enciphered, the rightmost rotor 
    always steps.
    Rule 2: Just before each letter is enciphered, if the top letter of any 
    rotor is its turnover, then that rotor and the rotor to its left step. 
    This rule does not apply to the leftmost rotor, however, since it has no 
    rotor to its left.
    Rule 3: No rotor steps more than once per letter enciphered, even if 
    the above rules could be construed as suggesting that a rotor would 
    step twice. *)

let rec stepcheck_topletter 
    (original:oriented_rotor list)
    (total:oriented_rotor list) 
    (* List of rotor positions that have been placed in list [total]. *)
    (total_positions: int list)
    (* Rotor that this recursion step is on. 0 is right-most rotor. *)
    (current_rotor_pos: int)  
  : oriented_rotor list = 
  match original with 
  | [] -> total
  | h :: [] ->
    if h.rotor.turnover=h.top_letter 
    then (
      (* If the rotor [h] is not already in the total list, then it has not 
          already been stepped, so add it. *)
      if (not (List.exists (fun x -> x = current_rotor_pos) total_positions)) 
      then (step_rotor h)::total
      else (
        (* If the rotor [step_rotor h] is not already in the total list, 
           then it has not already been stepped, so add it. 
           (This check avoids adding right-most rotor twice.) *)
        if (not (List.exists 
                   (fun x -> x = current_rotor_pos) total_positions)) 
        then h::total
        else
          total
      )
    )
    else (
      if (not (List.exists (fun x -> x = current_rotor_pos) total_positions))
      then h::total
      else total
    ) 
  | h1 :: h2 :: t ->
    if h1.rotor.turnover=h1.top_letter
    then (
      (* If the rotor [step_rotor h1] is not already in the total list, 
         then it has not already been stepped, so add it. *)
      if (not (List.exists (fun x -> x = current_rotor_pos) total_positions)) 
      then (
        (* If the rotor [step_rotor h2] is not already in the total list, 
           then it has not already been stepped, so add it. *)
        if (not (List.exists 
                   (fun x -> x = (current_rotor_pos+1)) total_positions)) 
        then
          stepcheck_topletter (h2::t) 
            ((step_rotor h2)::(step_rotor h1)::total)
            ((current_rotor_pos+1)::(current_rotor_pos)::total_positions)
            (current_rotor_pos + 1)
        else
          stepcheck_topletter (h2::t) 
            ((step_rotor h1)::total)
            ((current_rotor_pos)::total_positions)
            (current_rotor_pos + 1)
      )
      else
        (* If the rotor [step_rotor h2] is not already in the total list, 
           then it has not already been stepped, so add it. *)
      if (not (List.exists 
                 (fun x -> x = (current_rotor_pos+1)) total_positions)) 
      then (
        stepcheck_topletter (h2::t) 
          ((step_rotor h2)::total)
          ((current_rotor_pos+1)::total_positions)
          (current_rotor_pos + 1)
      )
      else
        stepcheck_topletter (h2::t) 
          total
          total_positions
          (current_rotor_pos + 1)
    )
    else (
      (* If the rotor [step_rotor h1] is not already in the total list, 
         then it has not already been stepped, so add it. 
         (This check avoids adding right-most rotor twice.) *)
      if (not (List.exists (fun x -> x = current_rotor_pos) total_positions)) 
      then (
        stepcheck_topletter (h2::t) 
          (h1::total)
          ((current_rotor_pos)::total_positions)
          (current_rotor_pos + 1)
      )
      else
        stepcheck_topletter (h2::t) 
          total
          total_positions
          (current_rotor_pos + 1)
    )

(** [step config] is the new configuration to which the Enigma machine 
      transitions when it steps beginning in configuration [config].
      Requires: [config] is a valid configuration. *)

let step (config:config) : config =
  {config with 
   rotors =
     (stepcheck_topletter (List.rev config.rotors) 
        [step_rotor (List.hd (List.rev config.rotors))] [0] 0)}

(** [cipher config s] is the string to which [s] enciphers
    when the Enigma machine begins in configuration [config].
    Requires:
      [config] is a valid configuration, and
      [s] contains only uppercase letters. *)

let rec cipher (config:config) (s:string) : string =
  match s with 
  | "" -> ""
  |  _ -> String.make 1 (cipher_char (step config) (String.get s 0) ) ^ 
          cipher (step config) (String.sub s 1 (String.length s - 1))

let hours_worked = [12; 12]
