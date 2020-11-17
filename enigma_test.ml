open OUnit2

open Enigma

(** [make_index_test name input expected_output] constructs an OUnit
    test named [name] that asserts the quality of [expected_output]
    with [index input]. *)

let make_index_test 
    (name : string) 
    (input: char) 
    (expected_output : int) : test = 
  name >:: (fun _ -> 
      assert_equal expected_output (index input) ~printer:string_of_int)

(* [rotor_input] represents a rotor with its wiring specs, top letter and
    the initial position at which current enters it, all specified in a record. *)

type rotor_input = {wiring:string; top_letter:char; input_pos:int}

(** [make_map_rl_lr_test] constructs an OUnit
    test named [name] that take a function [f] which determines whether 
    it is testing map_r_to_l or map_l_to_r and accordingly
    asserts the quality of int [expected_output] which is the output position 
    at which current appears 
    with f of [input] which applies the map function to the rotor specs. *)

let make_map_rl_lr_test f
    (name : string)
    (input: rotor_input)
    (expected_output : int) : test =
  name >:: (fun _ ->
      assert_equal expected_output 
        (f input.wiring input.top_letter input.input_pos)
        ~printer:string_of_int)

(** [make_map_r_to_l_test] constructs an OUnit
    test based on make_map_rl_lr_test where the function [f] is assigned
    to map_r_to_l. *)

let make_map_r_to_l_test = make_map_rl_lr_test map_r_to_l

(** [make_map_l_to_r_test] constructs an OUnit
    test based on make_map_rl_lr_test where the function [f] is assigned
    to map_l_to_r. *)

let make_map_l_to_r_test = make_map_rl_lr_test map_l_to_r

(** [make_map_refl_test] constructs an OUnit
    test named [name] that  
    asserts the quality of int [expected_output] which is the output position 
    at which current appears to map_refl applied on tuple [input] which is
    the position the current leaves the reflector based on the input position
    and wiring spec of the reflector given by the tuple. *)

let make_map_refl_test
    (name : string) 
    (input: string * int) 
    (expected_output : int) : test = 
  name >:: (fun _ -> 
      assert_equal expected_output 
        (map_refl (fst input) (snd input)) ~printer:string_of_int)

(** [make_map_plug_test] constructs an OUnit
    test named [name] that  
    asserts the quality of char [expected_output] which is the expected
    transformed character to the output of map_plug applied to the tuple
    [input] which contains the plugboard and input character. *)

let make_map_plug_test 
    (name : string) 
    (input: ((char*char) list)*char)
    (expected_output : char) : test = 
  name >:: (fun _ -> 
      assert_equal expected_output (map_plug (fst input) (snd input))
        ~printer:(String.make 1))

(** [make_cipher_char_test] constructs an OUnit
    test named [name] that  
    asserts the quality of char [expected_output] which is the expected
    ciphered character to the output of cipher_char applied to the tuple
    [input] which contains the configuration and input character. *)

let make_cipher_char_test 
    (name : string) 
    (input: config * char) 
    (expected_output : char) : test = 
  name >:: (fun _ -> 
      assert_equal expected_output 
        (cipher_char (fst input) (snd input)) ~printer:(String.make 1))

(** [topletter_rotors] returns a string of the updated topletters of the 
    rotors in oriented_rotor list [orl] due to stepping. *)

let rec topletter_rotors (orl: oriented_rotor list) = 
  match orl with 
  | [] -> ""
  | h :: t -> String.make 1 h.top_letter ^ topletter_rotors t

(** [make_step_test] constructs an OUnit
    test named [name] that  
    asserts the quality of string [expected_output] which is the expected
    topletters string to the output of applying step to the rotors contained
    in [input]. *)

let make_step_test
    (name : string) 
    (input: config) 
    (expected_output : string) : test = 
  name >:: (fun _ -> 
      assert_equal expected_output 
        (topletter_rotors ((step input).rotors)))

(** [make_cipher_test] constructs an OUnit
    test named [name] that  
    asserts the quality of string [expected_output] which is the expected
    enciphered string to the output of applying cipher to the [input]. *)

let make_cipher_test 
    (name : string)
    (input : config*string)
    (expected_output : string) : test =
  name >:: (fun _ ->
      assert_equal expected_output 
        (cipher (fst input) (snd input))
    )

(* Test cases testing the funcionality of the index function. *)

let index_tests = [
  make_index_test "index A" 'A' 0;
  make_index_test "index Z" 'Z' 25;
  make_index_test "index K" 'K' 10;
]

(* Test cases testing the funcionality of the map_r_to_l function. *)

let map_rl_tests = [
  make_map_r_to_l_test "Alphabet, orientation A, input 0" 
    {wiring = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"; top_letter = 'A'; input_pos = 0} 
    0;
  make_map_r_to_l_test "Example 1"
    {wiring = "EKMFLGDQVZNTOWYHXUSPAIBRCJ"; top_letter = 'A'; input_pos = 0} 
    4;
  make_map_r_to_l_test "BAC, orientation A, input 0"
    {wiring = "BACDEFGHIJKLMNOPQRSTUVWXYZ"; top_letter = 'A'; input_pos = 0} 
    1;
  make_map_r_to_l_test "BAC, orientation B, input 0"
    {wiring = "BACDEFGHIJKLMNOPQRSTUVWXYZ"; top_letter = 'B'; input_pos = 0} 
    25;
  make_map_r_to_l_test "BAC, orientation C, input 0"
    {wiring = "BACDEFGHIJKLMNOPQRSTUVWXYZ"; top_letter = 'C'; input_pos = 0} 
    0;
  make_map_r_to_l_test "Example 2"
    {wiring = "EKMFLGDQVZNTOWYHXUSPAIBRCJ"; top_letter = 'B'; input_pos = 0} 
    9;
  make_map_r_to_l_test "Rotor I"
    {wiring = "EKMFLGDQVZNTOWYHXUSPAIBRCJ"; top_letter = 'F'; input_pos = 5} 
    8;
  make_map_r_to_l_test "Example rotor_III"
    {wiring = "BDFHJLCPRTXVZNYEIWGAKMUSQO"; top_letter = 'O'; input_pos = 8} 
    6;
]

(* Test cases testing the funcionality of the map_l_to_r function. *)

let map_lr_tests = [
  make_map_l_to_r_test "Alphabet, orientation A, input 0" 
    {wiring = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"; top_letter = 'A'; input_pos = 0} 
    0;
  make_map_l_to_r_test "Example 3"
    {wiring = "EKMFLGDQVZNTOWYHXUSPAIBRCJ"; top_letter = 'A'; input_pos = 0} 
    20;
  make_map_l_to_r_test "Example 4"
    {wiring = "EKMFLGDQVZNTOWYHXUSPAIBRCJ"; top_letter = 'B'; input_pos = 0} 
    21;
  make_map_l_to_r_test "Example rotor_III"
    {wiring = "BDFHJLCPRTXVZNYEIWGAKMUSQO"; top_letter = 'O'; input_pos = 11} 
    24;
  make_map_l_to_r_test "Example rotor_I"
    {wiring = "EKMFLGDQVZNTOWYHXUSPAIBRCJ"; top_letter = 'F'; input_pos = 24} 
    1;
]

(* Test cases testing the funcionality of the map_refl function. *)

let map_refl_tests = [
  make_map_refl_test "Alphabet, input 0"
    ("ABCDEFGHIJKLMNOPQRSTUVWXYZ", 0) 0;
  make_map_refl_test "Reflector B, input 25"
    ("YRUHQSLDPXNGOKMIEBFZCWVJAT", 6) 11;
  make_map_refl_test "Reflector C, input 13"
    ("FVPJIAOYEDRZXWGCTKUQSBNMHL", 13) 22;

]

(* Test cases testing the funcionality of the map_plug function. *)

let map_plug_tests = [
  make_map_plug_test "empty list, input A"
    ([], 'A') 'A';
  make_map_plug_test "AZ,XY list, input X"
    ([('A','Z'); ('X','Y')], 'X') 'Y'; 
  make_map_plug_test "AZ,XY list, input Z"
    ([('A','Z'); ('X','Y')], 'Z') 'A'; 
  make_map_plug_test "YX,ZA list, input X"
    ([('Y','X'); ('Z','A')], 'X') 'Y'; 
  make_map_plug_test "YX,ZA list, input X"
    ([('Y','X'); ('Z','A')], 'Z') 'A';
  make_map_plug_test "Odd_Even flip list, input M"
    ([('A','B'); ('C','D'); ('E','F'); ('G','H'); 
      ('I','J'); ('K','L'); ('M','N'); ('O','P'); 
      ('Q','R'); ('S','T'); ('U','V'); ('W','X'); 
      ('Y','Z'); ], 'M') 'N'; 
]

let rotor_I = {rotor = {wiring = "EKMFLGDQVZNTOWYHXUSPAIBRCJ"; 
                        turnover = 'A'}; top_letter = 'F'}

let rotor_II = {rotor = {wiring = "AJDKSIRUXBLHWTMCQGZNPYFVOE"; 
                         turnover = 'A'}; top_letter = 'G'}

let rotor_III = {rotor = {wiring = "BDFHJLCPRTXVZNYEIWGAKMUSQO"; 
                          turnover = 'A'}; top_letter = 'O'}

let rotor_basic = {rotor = {wiring = "BDFHJLCPRTXVZNYEIWGAKMUSQO"; 
                            turnover = 'Z'}; top_letter = 'A'}

let rotor_basic_2 = {rotor = {wiring = "BDFHJLCPRTXVZNYEIWGAKMUSQO"; 
                              turnover = 'A'}; top_letter = 'A'}

let rotor_basic_3 = {rotor = {wiring = "BDFHJLCPRTXVZNYEIWGAKMUSQO"; 
                              turnover = 'A'}; top_letter = 'A'}

let rotor_basic_4 = {rotor = {wiring = "BDFHJLCPRTXVZNYEIWGAKMUSQO"; 
                              turnover = 'A'}; top_letter = 'A'}

let rotor_1 = {rotor = {wiring = "EKMFLGDQVZNTOWYHXUSPAIBRCJ"; 
                        turnover = 'Q'}; top_letter = 'F'}

let rotor_2 = {rotor = {wiring = "AJDKSIRUXBLHWTMCQGZNPYFVOE"; 
                        turnover = 'E'}; top_letter = 'U'}

let rotor_3 = {rotor = {wiring = "BDFHJLCPRTXVZNYEIWGAKMUSQO"; 
                        turnover = 'V'}; top_letter = 'N'}

(* Test cases testing the funcionality of the cipher_char function. *)

let cipher_char_tests = [
  make_cipher_char_test 
    "Alphabet reflector, no rotors, plugboard empty, input A"
    ({refl = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"; rotors = []; plugboard = []},
     'A') 'A';
  make_cipher_char_test
    "Reflector, Rotor I, Rotor III, Odd_Even flip plugboard, input F"
    ({refl = "YRUHQSLDPXNGOKMIEBFZCWVJAT"; rotors = [rotor_III; rotor_I];
      plugboard = [('A','B'); ('C','D'); ('E','F'); ('G','H'); 
                   ('I','J'); ('K','L'); ('M','N'); ('O','P'); 
                   ('Q','R'); ('S','T'); ('U','V'); ('W','X'); 
                   ('Y','Z'); ]},
     'F') 'S';
  make_cipher_char_test
    "Rotor II, Rotor III, rotor I, alphabet reflector, no plugboard"
    ({refl = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"; 
      rotors = [rotor_II; rotor_III; rotor_I]; 
      plugboard = []}, 'Z') 'Z'
]

(* Test cases testing the funcionality of the step function. *)

let step_tests = [
  make_step_test "Rule 1" ({refl = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"; 
                            rotors = [rotor_basic; rotor_basic; rotor_basic]; 
                            plugboard = []}) "AAB";
  make_step_test "Rule 2 and 3" 
    ({refl = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"; 
      rotors = [rotor_basic_2; rotor_basic_3; rotor_basic]; 
      plugboard = []}) "BBB";

  make_step_test "Rule 2 and 3 + edge" 
    ({refl = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"; 
      rotors = [rotor_basic_2; rotor_basic_3; rotor_basic_4]; 
      plugboard = []}) "BBB";

  make_step_test "Rule 1" 
    ({refl = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"; 
      rotors = [rotor_1; rotor_2; rotor_3]; 
      plugboard = []}) "FUO"

]

(* Test cases testing the funcionality of the cipher function. *)

let cipher_tests = [
  make_cipher_test "Test case given in A1"
    ({refl = "YRUHQSLDPXNGOKMIEBFZCWVJAT"; 
      rotors = [rotor_1; rotor_2; rotor_3]; 
      plugboard = [('A','Z')] }, "YNGXQ") "OCAML"
]

let tests =
  "test suite for A1"  >::: List.flatten [
    index_tests;
    map_rl_tests;
    map_lr_tests;
    map_refl_tests;
    map_plug_tests;
    cipher_char_tests;
    step_tests;
    cipher_tests;
  ]

let _ = run_test_tt_main tests
