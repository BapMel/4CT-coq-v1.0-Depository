(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require tacticext.
Require natprop.
Require seq.
Require cfmap.

Definition cf001 : config := (Config* 13 H 3 H 5 H 5 Y 4 H 4 Y 2 Y 1 Y).

Definition cf002 : config := (Config* 6 H 2 H 6 Y 4 H 1 Y 4 H 4 Y 2 Y Y).

Definition cf003 : config := (Config* 17 H 1 H 6 H 1 Y 4 H 6 H 6 H 6 Y Y 4 H
    1 Y 3 Y 1 Y).

Definition cf004 : config := (Config* 1 2 12 13 H 2 H 7 Y 5 H 1 Y 4 H 1 Y 4 Y
    2 Y 2 Y).

Definition cf005 : config := (Config* 10 H 6 H 1 Y 5 H 1 Y 4 H 1 Y 4 H 4 Y 2 Y
    Y).

Definition cf006 : config := (Config 19 H 2 H 8 Y 4 H 7 H 2 H 7 Y 6 H 1 Y 1 Y
    2 H 4 Y 2 Y Y).

Definition cf007 : config := (Config* 17 H 3 H 8 H 8 Y 6 H 1 Y 5 H 1 Y 5 Y 3 Y
    2 Y Y).

Definition cf008 : config := (Config* 6 H 2 H 7 Y 3 H 6 Y 2 H 1 H 1 Y H 4 Y Y
    1 Y).

Definition cf009 : config := (Config* 26 H 8 H 1 Y 7 H 7 H 1 Y 5 H 7 Y 3 H 6 H
    6 Y Y Y 3 Y Y).

Definition cf010 : config := (Config 20 H 2 H 9 Y 4 H 2 H 8 Y 3 H 1 Y 6 H 1 Y
    1 Y 2 H 4 Y 2 Y Y).

Definition cf011 : config := (Config* 1 2 8 9 H 8 H 1 Y 7 H 1 Y 5 H 1 H 6 H
    1 Y 2 H 6 Y Y Y 3 Y 2 Y).

Definition cf012 : config := (Config* 6 H 2 H 8 Y 3 H 7 Y 3 H 6 Y 2 H 1 Y H
    4 Y Y 1 Y).

Definition cf013 : config := (Config 23 H 3 H 9 H 9 Y 7 H 1 Y 5 H 2 H 7 Y 6 Y
    4 Y 3 Y 2 Y 1 Y).

Definition cf014 : config := (Config* 14 H 8 H 1 Y 7 H 1 Y 6 H 1 Y 5 H 1 Y 5 H
    5 Y 2 Y 3 Y 1 Y).

Definition cf015 : config := (Config 8 9 15 16 H 9 H 1 Y 8 H 8 H 1 Y 7 H 1 Y
    6 H 7 Y 2 H 6 Y Y Y 3 Y 2 Y).

Definition cf016 : config := (Config 30 H 2 H 10 Y 3 H 9 Y 5 H 8 H 2 H 8 Y 6 H
    1 H 1 Y 1 Y 1 Y 3 Y 2 Y 1 Y).

Definition cf017 : config := (Config* 26 H 2 H 10 Y 4 H 8 H 1 Y 3 H 8 Y 4 H 7 H
    7 Y 3 Y 4 Y 3 Y Y 1 Y).

Definition cf018 : config := (Config 26 H 9 H 1 Y 8 H 1 Y 6 H 2 H 8 Y 6 H 1 Y
    6 H 6 Y 3 Y 3 Y Y 1 Y).

Definition cf019 : config := (Config* 6 H 2 H 9 Y 3 H 8 Y 3 H 7 Y 2 H 1 H 1 Y
    H 5 Y Y Y 1 Y).

Definition cf020 : config := (Config 1 2 8 9 H 10 H 1 Y 9 H 1 Y 8 H 7 H 2 H 9 Y
    5 Y 3 H 7 H 7 Y Y Y 3 Y 1 Y 2 Y).

Definition cf021 : config := (Config* 6 H 2 H 10 Y 3 H 9 Y 3 H 8 Y 3 H 7 Y 2 H
    1 Y H 5 Y Y Y 1 Y).

Definition cf022 : config := (Config 29 H 2 H 11 Y 3 H 10 Y 4 H 8 H 1 Y 3 H 8 Y
    2 H 1 H 1 Y 5 Y 3 Y 1 Y Y 1 Y).

Definition cf023 : config := (Config 1 2 8 9 H 2 H 12 Y 3 H 11 Y 3 H 2 H 10 Y
    3 H 9 Y 5 Y 6 H 1 H 1 Y 1 Y 1 Y 3 Y 2 Y 1 Y).

Definition cf024 : config := (Config* 6 H 2 H 7 Y 5 H 1 Y 5 H 5 H 5 Y 3 Y Y Y
   ).

Definition cf025 : config := (Config* 25 H 3 H 7 H 1 Y 4 H 1 H 1 H 1 Y 1 Y 1 Y
    2 H 4 Y 2 Y 1 Y).

Definition cf026 : config := (Config 19 H 7 H 1 Y 3 H 7 Y 4 H 5 H 1 Y 2 Y 3 Y
    1 Y 2 Y).

Definition cf027 : config := (Config 6 H 2 H 8 Y 6 H 1 Y 4 H 6 Y 3 H 1 Y 4 H
    1 Y 3 Y 1 Y).

Definition cf028 : config := (Config 26 H 2 H 9 Y 4 H 3 H 7 H 1 Y 5 H 1 H 1 Y
    1 Y 1 Y 1 Y 2 Y 1 Y).

Definition cf029 : config := (Config* 4 5 21 25 H 8 H 1 Y 7 H 1 Y 5 H 1 H 6 H
    1 Y 6 H 1 Y 1 Y 1 Y 1 Y 2 Y).

Definition cf030 : config := (Config 19 H 2 H 9 Y 4 H 8 H 2 H 8 Y 7 H 1 Y 1 Y
    3 H 5 H 5 Y 3 Y Y Y).

Definition cf031 : config := (Config 18 H 2 H 9 Y 6 H 8 H 2 H 8 Y 2 H 7 Y Y
    5 H 1 Y 4 H 1 Y 3 Y 1 Y).

Definition cf032 : config := (Config 23 H 2 H 9 Y 7 H 1 Y 4 H 3 H 7 H 7 Y 6 Y
    4 Y Y 3 Y 1 Y).

Definition cf033 : config := (Config 24 H 3 H 9 H 9 Y 6 H 2 H 8 Y 6 H 1 Y 6 Y
    4 Y Y 2 Y 2 Y).

Definition cf034 : config := (Config 15 H 8 H 1 Y 7 H 1 Y 5 H 2 H 7 Y 5 H 1 Y
    4 Y 3 Y Y 2 Y).

Definition cf035 : config := (Config 6 H 2 H 9 Y 7 H 1 Y 6 H 1 Y 5 H 6 Y 4 Y
    4 H 4 Y 2 Y Y).

Definition cf036 : config := (Config* 23 H 7 H 1 H 1 Y 3 H 8 Y 4 H 6 H 1 Y 2 Y
    3 Y 1 Y 1 Y 2 Y).

Definition cf037 : config := (Config* 23 H 2 H 9 Y 7 H 1 Y 5 H 2 H 7 Y 6 H 6 Y
    4 Y 2 Y 2 Y 1 Y).

Definition cf038 : config := (Config 10 H 2 H 8 Y 3 H 7 Y 3 H 6 Y 2 H 1 H 1 Y
    H 4 Y Y 1 Y).

Definition cf039 : config := (Config* 1 2 8 9 H 2 H 10 Y 3 H 9 Y 3 H 3 H 7 H
    1 Y 6 H 1 Y 1 Y 1 Y 1 Y 2 Y 1 Y).

Definition cf040 : config := (Config 11 12 21 26 H 2 H 10 Y 4 H 2 H 9 Y 3 H 8 Y
    5 H 1 H 1 Y 1 Y 1 Y 1 Y 2 Y 1 Y).

Definition cf041 : config := (Config 20 H 2 H 10 Y 5 H 2 H 9 Y 3 H 1 Y 7 H 1 Y
    1 Y 3 H 5 H 5 Y 3 Y Y Y).

Definition cf042 : config := (Config 23 H 2 H 10 Y 3 H 9 Y 4 H 8 H 2 H 8 Y 7 H
    1 Y 1 Y 2 H 5 Y Y 1 Y 2 Y).

Definition cf043 : config := (Config 30 H 8 H 2 H 10 Y 8 H 1 Y 6 H 1 H 7 H 1 Y
    2 H 7 Y Y Y 3 Y 1 Y 2 Y).

Definition cf044 : config := (Config 25 H 2 H 10 Y 4 H 8 H 1 Y 4 H 8 H 2 H 8 Y
    2 H 7 Y Y Y Y 3 Y 1 Y).

Definition cf045 : config := (Config* 24 H 6 H 3 H 9 H 9 Y 6 H 1 H 7 H 1 Y 2 H
    7 Y Y Y 4 H 4 Y 2 Y Y).

Definition cf046 : config := (Config 18 H 8 H 1 Y 6 H 1 H 7 H 1 Y 2 H 7 Y Y
    4 H 1 H 1 Y H 4 Y Y 1 Y).

Definition cf047 : config := (Config* 25 H 3 H 10 H 10 Y 8 H 1 Y 7 H 1 Y 6 H 1 Y
    6 Y 4 Y 2 Y 3 Y Y).

Definition cf048 : config := (Config 27 H 2 H 9 Y 3 H 8 Y 3 H 7 Y 4 H 5 H 1 Y
    H 5 Y Y 1 Y 2 Y).

Definition cf049 : config := (Config 28 H 2 H 10 Y 3 H 9 Y 3 H 8 Y 4 H 6 H 1 Y
    2 H 1 Y 5 Y 4 Y 3 Y Y).

Definition cf050 : config := (Config 27 H 9 H 1 Y 7 H 2 H 9 Y 7 H 1 Y 6 H 1 Y
    6 H 6 Y 2 Y 2 Y 2 Y 1 Y).

Definition cf051 : config := (Config 14 H 9 H 1 Y 8 H 1 Y 7 H 1 Y 6 H 1 Y 6 H
    6 H 6 Y 3 Y Y 3 Y 1 Y).

Definition cf052 : config := (Config 24 H 3 H 9 H 1 Y 3 H 9 Y 3 H 8 Y 3 H 7 Y
    2 H 1 Y 1 Y 3 Y 3 Y Y).

Definition cf053 : config := (Config 23 H 9 H 1 Y 6 H 3 H 9 H 9 Y 7 H 1 Y 6 H
    1 Y 5 Y Y 3 Y 1 Y 1 Y).

Definition cf054 : config := (Config 28 H 3 H 10 H 10 Y 7 H 2 H 9 Y 6 H 2 H 8 Y
    7 Y 5 Y Y 3 Y 2 Y Y).

Definition cf055 : config := (Config 28 H 9 H 1 Y 8 H 1 Y 6 H 2 H 8 Y 6 H 1 Y
    4 Y 2 H 1 Y 1 Y Y 2 Y).

Definition cf056 : config := (Config 28 H 9 H 1 Y 8 H 1 Y 5 H 3 H 8 H 8 Y 6 H
    1 Y 5 Y 3 Y 1 Y 2 Y Y).

Definition cf057 : config := (Config 7 H 3 H 10 H 10 Y 8 H 1 Y 7 H 1 Y 6 H 7 Y
    5 Y 4 H 5 Y 3 Y Y Y).

Definition cf058 : config := (Config 26 H 3 H 10 H 10 Y 8 H 1 Y 5 H 3 H 8 H 8 Y
    7 Y 5 Y Y Y 3 Y 1 Y).

Definition cf059 : config := (Config 28 H 9 H 1 Y 7 H 2 H 9 Y 7 H 1 Y 6 H 1 Y
    6 H 6 Y Y Y 2 Y 2 Y).

Definition cf060 : config := (Config 21 H 2 H 10 Y 7 H 2 H 9 Y 5 H 3 H 8 H 8 Y
    7 Y 4 Y 1 Y 3 Y 2 Y Y).

Definition cf061 : config := (Config 6 H 2 H 10 Y 8 H 1 Y 7 H 1 Y 5 H 7 Y 2 H
    1 H 1 Y 1 Y Y 3 Y 1 Y).

Definition cf062 : config := (Config 8 9 15 16 H 2 H 11 Y 3 H 2 H 10 Y 3 H 9 Y
    Y 4 H 7 H 7 H 7 Y Y Y 4 Y Y Y).

Definition cf063 : config := (Config 31 H 10 H 1 Y 9 H 8 H 2 H 10 Y 8 H 1 Y 7 H
    8 Y 2 H 7 Y Y Y 3 Y 1 Y 2 Y).

Definition cf064 : config := (Config 4 5 22 27 H 2 H 11 Y 3 H 10 Y 3 H 2 H 9 Y
    3 H 8 Y 6 H 7 Y Y Y 4 H 1 Y 3 Y 1 Y).

Definition cf065 : config := (Config 31 H 2 H 11 Y 4 H 2 H 10 Y 4 H 8 H 1 Y 8 Y
    6 H 1 H 1 Y 1 Y 1 Y 1 Y 2 Y 1 Y).

Definition cf066 : config := (Config 1 2 8 9 H 2 H 11 Y 3 H 10 Y 4 H 3 H 8 H
    1 Y 7 H 1 Y 7 H 1 Y 1 Y 1 Y 1 Y 2 Y 1 Y).

Definition cf067 : config := (Config 34 H 10 H 1 Y 8 H 2 H 10 Y 6 H 1 H 8 H 1 Y
    3 H 8 H 8 Y Y Y 3 Y 1 Y 3 Y Y).

Definition cf068 : config := (Config 32 H 9 H 2 H 11 Y 9 H 1 Y 6 H 1 H 8 H 1 Y
    8 H 1 Y 1 Y 2 H 6 Y 5 Y 3 Y 1 Y 1 Y).

Definition cf069 : config := (Config* 25 H 10 H 1 Y 9 H 9 H 1 Y 7 H 1 H 8 H 1 Y
    2 H 8 Y Y Y 4 H 1 Y 4 Y 2 Y Y).

Definition cf070 : config := (Config 33 H 2 H 10 Y 3 H 2 H 9 Y 5 H 8 H 7 H 1 H
    1 H 1 Y 1 Y Y 1 Y 1 Y 2 Y 1 Y).

Definition cf071 : config := (Config 21 H 9 H 1 Y 7 H 8 H 1 Y 6 H 1 H 1 H 8 H
    8 Y Y 1 Y Y 4 H 1 Y 3 Y 1 Y).

Definition cf072 : config := (Config 25 H 9 H 1 Y 8 H 6 H 3 H 9 H 9 Y 7 H 8 Y
    2 H 7 Y Y Y 4 H 4 Y 2 Y Y).

Definition cf073 : config := (Config 25 H 2 H 11 Y 3 H 10 Y 3 H 9 Y 3 H 8 Y 3 H
    7 Y 2 H 1 Y 4 Y 3 Y 1 Y Y).

Definition cf074 : config := (Config 15 H 10 H 1 Y 9 H 1 Y 7 H 2 H 9 Y 7 H 1 Y
    6 H 1 Y 5 Y 3 Y 3 Y 3 Y 1 Y).

Definition cf075 : config := (Config 15 29 H 3 H 11 H 11 Y 9 H 1 Y 8 H 1 Y 6 H
    2 H 8 Y 7 Y 5 Y 3 Y 3 Y Y Y).

Definition cf076 : config := (Config* 27 H 10 H 1 Y 9 H 1 Y 8 H 1 Y 7 H 1 Y 6 H
    1 Y 6 H 6 Y 2 Y 4 Y Y Y).

Definition cf077 : config := (Config* 14 H 2 H 9 Y 3 H 8 Y 3 H 7 Y 3 H 6 Y 2 H
    1 H 1 Y H 4 Y Y 1 Y).

Definition cf078 : config := (Config 14 H 2 H 10 Y 3 H 9 Y 3 H 8 Y 3 H 7 Y 2 H
    1 H 1 Y 1 Y 4 H 1 Y 3 Y 1 Y).

Definition cf079 : config := (Config 18 H 2 H 11 Y 3 H 10 Y 3 H 9 Y 3 H 8 Y 3 H
    7 Y 3 H 5 H 1 Y 2 Y 1 Y Y Y).

Definition cf080 : config := (Config 27 H 3 H 10 H 1 Y 3 H 10 Y 3 H 9 Y 3 H 8 Y
    2 H 1 H 1 Y 1 Y 4 Y 3 Y Y Y).

Definition cf081 : config := (Config 30 H 10 H 1 Y 9 H 1 Y 6 H 3 H 9 H 9 Y 7 H
    1 Y 7 H 7 Y 3 Y 1 Y 3 Y Y 1 Y).

Definition cf082 : config := (Config 14 H 9 H 1 Y 8 H 1 Y 7 H 1 Y 6 H 1 Y 5 H
    1 H 1 Y H 5 Y Y Y 1 Y).

Definition cf083 : config := (Config 4 5 25 30 H 11 H 1 Y 10 H 1 Y 9 H 9 H 1 Y
    8 H 1 Y 8 H 8 H 8 Y Y Y Y 3 Y 1 Y 1 Y).

Definition cf084 : config := (Config 20 H 10 H 1 Y 9 H 1 Y 7 H 8 H 1 Y 7 H 1 Y
    3 H 1 H 1 Y 1 Y Y 3 Y 1 Y 1 Y).

Definition cf085 : config := (Config 30 H 10 H 1 Y 9 H 1 Y 6 H 3 H 9 H 9 Y 7 H
    1 Y 7 H 1 Y 1 Y Y 3 Y 1 Y Y).

Definition cf086 : config := (Config 26 H 10 H 1 Y 9 H 1 Y 5 H 4 H 9 H 9 H 9 Y
    7 H 1 Y 5 Y 4 Y 1 Y 3 Y Y Y).

Definition cf087 : config := (Config 25 H 11 H 1 Y 10 H 1 Y 8 H 9 H 1 Y 3 H 1 Y
    1 Y 7 H 1 Y 1 Y 3 H 5 H 5 Y 3 Y Y Y).

Definition cf088 : config := (Config 35 H 11 H 1 Y 10 H 10 H 1 Y 8 H 2 H 10 Y 7 H
    9 Y 3 H 8 H 8 Y Y Y 3 Y 1 Y 3 Y Y).

Definition cf089 : config := (Config 8 9 15 16 H 10 H 1 Y 9 H 9 H 1 Y 8 H 1 Y
    6 H 1 H 1 H 8 H 8 Y Y 1 Y Y Y 3 Y 1 Y).

Definition cf090 : config := (Config* 14 15 21 22 H 8 H 3 H 11 H 11 Y 9 H 9 H
    1 Y 8 H 1 Y 6 H 8 Y 3 H 7 Y Y Y Y 3 Y 1 Y).

Definition cf091 : config := (Config 34 H 11 H 1 Y 9 H 2 H 11 Y 9 H 1 Y 7 H
    1 H 8 H 1 Y 8 H 1 Y 1 Y 2 H 6 Y Y Y Y Y).

Definition cf092 : config := (Config 28 H 8 H 3 H 11 H 11 Y 9 H 1 Y 7 H 1 H
    8 H 1 Y 2 H 8 Y Y Y 5 H 5 Y 2 Y 3 Y 1 Y).

Definition cf093 : config := (Config 22 H 10 H 1 Y 9 H 1 Y 7 H 1 H 8 H 1 Y 2 H
    8 Y Y 5 H 1 H 1 Y H 5 Y Y Y 1 Y).

Definition cf094 : config := (Config 25 H 10 H 1 Y 9 H 9 H 1 Y 8 H 1 Y 6 H 1 H
    1 H 8 H 8 Y Y 1 Y Y 4 H 1 Y 3 Y 1 Y).

Definition cf095 : config := (Config 28 H 2 H 12 Y 3 H 11 Y 3 H 10 Y 3 H 9 Y
    3 H 8 Y 2 H 1 H 1 Y 5 Y 3 Y 1 Y Y Y).

Definition cf096 : config := (Config 27 H 11 H 1 Y 10 H 1 Y 8 H 2 H 10 Y 8 H 1 Y
    7 H 1 Y 7 H 7 Y 3 Y 4 Y Y 1 Y Y).

Definition cf097 : config := (Config 26 H 2 H 11 Y 3 H 10 Y 3 H 9 Y 3 H 8 Y 4 H
    7 H 7 Y Y 2 H 1 Y 1 Y 1 Y Y).

Definition cf098 : config := (Config 26 H 3 H 11 H 11 Y 9 H 1 Y 8 H 1 Y 6 H
    2 H 8 Y 7 Y 1 Y 5 H 5 Y Y Y 1 Y).

Definition cf099 : config := (Config 18 H 10 H 1 Y 9 H 1 Y 8 H 1 Y 7 H 1 Y 6 H
    1 Y 6 H 1 Y H 5 Y Y Y 1 Y).

Definition cf100 : config := (Config* 27 H 2 H 11 Y 3 H 10 Y 3 H 9 Y 3 H 8 Y
    2 H 1 H 1 Y H 6 Y Y Y Y Y).

Definition cf101 : config := (Config 31 H 3 H 12 H 12 Y 10 H 1 Y 9 H 1 Y 8 H
    8 H 1 Y 8 Y 6 Y 5 H 6 Y 3 Y Y 3 Y 1 Y).

Definition cf102 : config := (Config 31 H 11 H 1 Y 10 H 1 Y 8 H 2 H 10 Y 8 H 1 Y
    6 H 1 H 1 Y 6 Y 3 Y 4 Y Y 3 Y 1 Y).

Definition cf103 : config := (Config 33 H 11 H 1 Y 10 H 1 Y 9 H 1 Y 7 H 2 H 9 Y
    7 H 1 Y 7 H 7 Y 3 Y 4 Y Y Y Y).

Definition cf104 : config := (Config* 31 33 H 3 H 12 H 12 Y 10 H 1 Y 8 H 2 H
    10 Y 7 H 2 H 9 Y 8 Y 5 Y 4 Y 4 Y Y Y Y).

Definition cf105 : config := (Config 6 H 9 H 1 Y 8 H 1 Y 7 H 1 Y 6 H 1 Y 5 H
    1 H 6 H 1 H 1 Y 1 Y 1 Y Y Y).

Definition cf106 : config := (Config 33 H 2 H 12 Y 3 H 11 Y 4 H 2 H 10 Y 3 H
    9 Y 6 H 1 H 1 Y 1 Y Y 2 H 1 Y 1 Y 1 Y 1 Y).

Definition cf107 : config := (Config 29 H 11 H 1 Y 10 H 10 H 1 Y 7 H 3 H 10 H 10 Y
    8 H 9 Y 2 H 8 Y Y Y 3 H 1 Y 1 Y 1 Y Y).

Definition cf108 : config := (Config 23 H 11 H 1 Y 8 H 10 H 1 Y 9 H 1 Y 8 H 9 Y
    2 H 8 Y Y 5 H 1 H 1 Y H 5 Y Y Y 1 Y).

Definition cf109 : config := (Config 6 H 10 H 1 Y 9 H 1 Y 8 H 1 Y 7 H 1 Y 5 H
    2 H 7 Y H 1 H 1 Y 1 Y 1 Y Y Y).

Definition cf110 : config := (Config 32 H 12 H 1 Y 11 H 1 Y 9 H 2 H 11 Y 9 H
    1 Y 8 H 1 Y 7 H 8 Y 2 H 1 Y 5 Y Y 3 Y 1 Y 1 Y).

Definition cf111 : config := (Config 23 H 8 H 1 Y 6 H 2 H 8 Y 6 H 1 Y 5 H 1 Y
    4 Y Y 3 Y Y).

Definition cf112 : config := (Config* 23 H 2 H 9 Y 7 H 1 Y 6 H 6 H 1 Y 6 Y 3 H
    1 Y 4 Y 1 Y 2 Y).

Definition cf113 : config := (Config* 6 H 8 H 1 Y 3 H 8 Y 5 H 1 Y 4 H 6 Y 3 H
    5 H 5 Y 3 Y Y Y).

Definition cf114 : config := (Config 25 H 2 H 10 Y 3 H 9 Y 4 H 8 H 2 H 8 Y 3 H
    7 H 7 Y Y Y Y 3 Y Y).

Definition cf115 : config := (Config 25 H 2 H 10 Y 4 H 9 H 2 H 9 Y 3 H 8 H 8 Y
    Y Y 4 H 5 H 5 Y 3 Y Y Y).

Definition cf116 : config := (Config* 1 2 19 24 H 9 H 1 Y 3 H 9 Y 4 H 7 H 1 Y
    3 H 7 Y 2 Y 3 Y 4 Y 3 Y Y).

Definition cf117 : config := (Config 14 H 8 H 1 Y 7 H 1 Y 6 H 1 Y 6 H 6 H 6 Y
    1 H 1 Y 1 Y Y 2 Y).

Definition cf118 : config := (Config 23 H 9 H 1 Y 7 H 2 H 9 Y 7 H 1 Y 6 H 1 Y
    4 Y Y 2 H 1 Y 1 Y Y).

Definition cf119 : config := (Config 6 H 9 H 1 Y 3 H 9 Y 4 H 2 H 8 Y 2 Y 4 H
    6 Y 2 H 5 Y 3 Y Y Y).

Definition cf120 : config := (Config* 6 H 9 H 1 Y 3 H 9 Y 6 H 5 H 1 H 1 H 1 Y
    2 Y 3 Y 1 Y 3 Y Y Y).

Definition cf121 : config := (Config 28 H 3 H 9 H 1 Y 3 H 9 Y 3 H 8 Y 4 H 7 H
    7 Y 3 Y 1 Y 3 Y 1 Y 2 Y).

Definition cf122 : config := (Config 27 H 3 H 10 H 10 Y 6 H 3 H 9 H 9 Y 7 H 1 Y
    7 Y 5 Y Y Y 3 Y Y).

Definition cf123 : config := (Config 27 H 2 H 10 Y 3 H 9 Y 3 H 8 Y 3 H 1 H 1 Y
    5 H 1 Y 5 Y 1 Y 2 Y 1 Y).

Definition cf124 : config := (Config 12 13 28 H 2 H 10 Y 3 H 9 Y 3 H 8 Y 4 H
    6 H 1 Y 4 Y 5 H 5 Y Y 1 Y 2 Y).

Definition cf125 : config := (Config 26 H 3 H 10 H 10 Y 8 H 1 Y 7 H 7 H 1 Y 7 Y
    5 Y 5 H 5 Y 2 Y Y 2 Y).

Definition cf126 : config := (Config 13 H 9 H 1 Y 7 H 2 H 9 Y 7 H 1 Y 5 H 1 H
    1 Y 5 Y Y Y 3 Y Y).

Definition cf127 : config := (Config 31 H 3 H 10 H 1 Y 3 H 3 H 9 H 1 Y 3 H 9 Y
    2 H 1 Y 1 Y 1 Y 1 Y 3 Y Y Y).

Definition cf128 : config := (Config 4 5 18 23 H 2 H 11 Y 3 H 10 Y 5 H 2 H 9 Y
    2 H 1 Y 1 Y 1 Y 3 H 5 H 5 Y 3 Y Y Y).

Definition cf129 : config := (Config 26 H 2 H 11 Y 5 H 2 H 10 Y 3 H 9 Y 5 H 8 Y
    3 H 7 H 7 Y Y Y Y 3 Y Y).

Definition cf130 : config := (Config 6 H 9 H 1 Y 3 H 9 Y 3 H 8 Y 4 H 1 Y 6 H
    1 Y 4 H 5 Y 1 H 1 Y 1 Y Y).

Definition cf131 : config := (Config 29 H 2 H 11 Y 3 H 10 Y 4 H 9 H 2 H 9 Y 3 H
    8 H 8 Y Y Y 3 H 5 Y 3 Y Y Y).

Definition cf132 : config := (Config 32 H 4 H 9 H 1 H 1 Y 3 H 10 Y 4 H 9 H 2 H
    9 Y 2 H 8 Y Y Y 2 Y 3 Y Y Y).

Definition cf133 : config := (Config 34 H 9 H 2 H 11 Y 9 H 1 Y 7 H 1 H 8 H 1 Y
    2 H 8 Y Y 6 H 1 Y 5 Y 1 Y 3 Y Y).

Definition cf134 : config := (Config 19 H 2 H 10 Y 4 H 9 H 2 H 9 Y 8 H 1 Y 1 Y
    2 H 6 Y 2 H 1 H 1 Y 4 H 1 Y 3 Y 1 Y).

Definition cf135 : config := (Config* 13 H 8 H 1 H 1 Y 3 H 9 Y 3 H 8 Y 3 H 7 Y
    2 Y 2 H 1 Y 4 Y 1 Y 2 Y).

Definition cf136 : config := (Config 14 H 9 H 1 Y 8 H 1 Y 7 H 1 Y 6 H 1 Y 6 H
    6 Y 1 H 1 Y 1 Y Y 2 Y).

Definition cf137 : config := (Config 29 H 10 H 1 Y 9 H 1 Y 8 H 1 Y 7 H 1 Y 6 H
    1 Y 6 H 6 Y 2 Y 2 Y 2 Y 1 Y).

Definition cf138 : config := (Config 18 19 29 H 10 H 1 Y 3 H 10 Y 5 H 7 H 1 H
    1 Y 3 H 8 Y 2 Y 3 Y 1 Y 3 Y Y Y).

Definition cf139 : config := (Config 7 H 3 H 11 H 11 Y 8 H 2 H 10 Y 8 H 1 Y 7 H
    1 Y 7 Y 5 Y Y 3 Y 2 Y 2 Y).

Definition cf140 : config := (Config 12 13 29 H 2 H 11 Y 3 H 10 Y 3 H 9 Y 3 H
    8 Y 3 H 7 Y 4 Y 5 H 5 Y Y 1 Y 2 Y).

Definition cf141 : config := (Config* 29 H 10 H 1 Y 3 H 10 Y 3 H 9 Y 3 H 2 H 8 Y
    2 Y 3 Y 4 Y 4 H 4 Y 2 Y Y).

Definition cf142 : config := (Config 29 H 3 H 11 H 11 Y 9 H 1 Y 8 H 1 Y 7 H
    1 Y 7 H 7 Y 5 Y 2 Y 2 Y 2 Y 2 Y).

Definition cf143 : config := (Config 17 22 23 28 H 9 H 1 H 1 Y 3 H 10 Y 4 H 8 H
    1 Y 3 H 8 Y 2 Y 3 Y 5 Y 4 Y 3 Y 1 Y).

Definition cf144 : config := (Config 14 H 2 H 11 Y 3 H 10 Y 3 H 9 Y 3 H 8 Y 4 H
    7 H 7 Y 3 Y 4 Y 1 Y 2 Y 1 Y).

Definition cf145 : config := (Config 5 19 27 29 H 3 H 11 H 11 Y 9 H 1 Y 7 H
    2 H 9 Y 7 H 1 Y 7 Y 5 Y Y Y 3 Y Y).

Definition cf146 : config := (Config 26 H 9 H 2 H 11 Y 9 H 1 Y 7 H 2 H 9 Y 7 H
    1 Y 7 H 7 Y Y 3 Y 1 Y 2 Y 1 Y).

Definition cf147 : config := (Config 30 H 8 H 3 H 11 H 11 Y 9 H 1 Y 8 H 1 Y
    6 H 1 H 1 Y 6 Y Y Y 3 Y 1 Y Y).

Definition cf148 : config := (Config 13 H 10 H 1 Y 8 H 2 H 10 Y 8 H 1 Y 7 H 1 Y
    6 H 7 Y Y Y 2 H 1 Y 1 Y Y).

Definition cf149 : config := (Config 29 H 9 H 1 H 1 Y 3 H 10 Y 6 H 6 H 1 H 1 H
    1 Y 2 Y 3 Y 1 Y 1 Y 3 Y Y Y).

Definition cf150 : config := (Config 32 H 10 H 1 Y 9 H 1 Y 8 H 8 H 1 Y 7 H 1 Y
    7 H 7 Y 5 H 6 Y 3 Y Y Y 2 Y).

Definition cf151 : config := (Config 31 H 10 H 1 Y 9 H 1 Y 7 H 2 H 9 Y 7 H 1 Y
    7 H 7 H 7 Y Y Y Y 3 Y Y).

Definition cf152 : config := (Config 4 5 22 27 H 2 H 12 Y 3 H 11 Y 4 H 2 H 10 Y
    3 H 9 Y 2 H 1 Y 1 Y 1 Y 2 H 5 Y 3 Y Y Y).

Definition cf153 : config := (Config 32 H 3 H 11 H 11 Y 9 H 1 Y 8 H 1 Y 6 H
    8 Y 6 Y 4 H 1 H 1 Y 4 Y Y 1 Y 1 Y).

Definition cf154 : config := (Config 29 H 9 H 2 H 11 Y 9 H 1 Y 6 H 3 H 9 H 9 Y
    7 H 1 Y 5 Y 1 Y 3 Y 1 Y Y 1 Y).

Definition cf155 : config := (Config 26 H 4 H 11 H 11 H 11 Y 9 H 1 Y 8 H 1 Y
    7 H 8 Y 5 Y 1 Y 4 H 5 Y Y 1 Y 1 Y).

Definition cf156 : config := (Config 29 H 4 H 11 H 11 H 11 Y 9 H 1 Y 6 H 3 H
    9 H 9 Y 8 Y 5 Y 1 Y 3 Y Y 1 Y 1 Y).

Definition cf157 : config := (Config 6 H 10 H 1 Y 3 H 10 Y 3 H 9 Y 5 H 1 Y 7 H
    7 H 7 H 7 Y Y 1 Y 3 Y Y Y).

Definition cf158 : config := (Config 6 H 10 H 1 Y 3 H 10 Y 3 H 9 Y 5 H 1 Y 5 H
    7 Y 3 H 1 Y 5 H 1 Y 3 Y 1 Y 1 Y).

Definition cf159 : config := (Config 1 2 32 H 10 H 1 Y 9 H 1 Y 8 H 1 Y 5 H 3 H
    8 H 8 Y 7 H 1 Y 1 Y Y 3 Y 1 Y 2 Y).

Definition cf160 : config := (Config 30 H 2 H 12 Y 3 H 11 Y 3 H 2 H 10 Y 2 H
    9 Y 3 H 8 H 8 Y Y Y 3 H 5 Y 3 Y Y Y).

Definition cf161 : config := (Config 30 H 2 H 12 Y 3 H 11 Y 4 H 2 H 10 Y 9 H
    1 Y 3 H 8 H 8 Y Y Y 3 H 5 Y 3 Y Y Y).

Definition cf162 : config := (Config 33 H 4 H 10 H 1 H 1 Y 3 H 11 Y 3 H 2 H 10 Y
    2 H 9 Y 2 H 8 Y Y Y 2 Y 3 Y Y Y).

Definition cf163 : config := (Config 33 H 4 H 10 H 1 H 1 Y 3 H 11 Y 4 H 2 H 10 Y
    9 H 1 Y 2 H 8 Y Y Y 2 Y 3 Y Y Y).

Definition cf164 : config := (Config 35 H 3 H 11 H 1 Y 4 H 3 H 10 H 1 Y 3 H 10 Y
    2 H 1 Y 3 H 8 Y Y 1 Y 1 Y 3 Y Y Y).

Definition cf165 : config := (Config 36 H 11 H 1 Y 10 H 1 Y 8 H 9 H 1 Y 8 H 1 Y
    8 H 8 Y 4 H 7 Y Y 1 Y 2 H 1 Y 3 Y 1 Y).

Definition cf166 : config := (Config 11 12 18 19 H 10 H 2 H 12 Y 8 H 10 H 1 Y
    9 H 1 Y 1 Y 8 H 1 Y 1 Y 3 H 6 H 6 Y 5 Y 4 Y Y Y).

Definition cf167 : config := (Config 33 H 10 H 2 H 12 Y 10 H 1 Y 9 H 1 Y 7 H 1 H
    8 H 1 Y 8 H 1 Y 1 Y 1 Y 5 Y 4 Y Y Y).

Definition cf168 : config := (Config 35 H 2 H 12 Y 3 H 2 H 11 Y 4 H 9 H 1 Y
    4 H 1 Y 7 H 1 H 1 Y 1 Y 1 Y 4 Y 1 Y 3 Y Y).

Definition cf169 : config := (Config* 11 12 18 19 H 10 H 2 H 12 Y 9 H 10 H 1 Y
    9 H 1 Y 1 Y 7 H 1 H 1 Y 1 Y 2 H 6 Y 4 Y 1 Y 3 Y Y).

Definition cf170 : config := (Config 38 H 4 H 10 H 1 H 1 Y 3 H 11 Y 5 H 10 H 2 H
    10 Y 2 H 9 Y Y 7 H 1 Y 2 Y 4 Y Y Y Y).

Definition cf171 : config := (Config 26 H 2 H 12 Y 4 H 2 H 11 Y 4 H 10 H 2 H
    10 Y 9 H 1 Y 1 Y 1 Y 4 H 6 H 6 Y 3 Y Y 3 Y 1 Y).

Definition cf172 : config := (Config 34 H 2 H 12 Y 3 H 11 Y 4 H 10 H 2 H 10 Y
    9 H 1 Y 1 Y 3 H 7 H 7 Y 3 H 6 Y Y 3 Y Y Y).

Definition cf173 : config := (Config 36 H 10 H 1 Y 9 H 9 H 1 Y 5 H 1 H 3 H 9 H
    9 H 9 H 9 Y Y 1 Y Y Y 4 Y Y Y).

Definition cf174 : config := (Config 36 H 10 H 1 Y 7 H 9 H 1 Y 9 H 9 H 1 H 1 Y
    4 H 8 H 8 H 8 Y Y Y Y 4 Y Y Y).

Definition cf175 : config := (Config 20 H 2 H 11 Y 3 H 2 H 10 Y 2 H 9 Y 8 H 1 Y
    1 Y 2 H 6 Y 2 H 1 H 1 Y H 4 Y Y 1 Y).

Definition cf176 : config := (Config 20 H 2 H 11 Y 6 H 2 H 10 Y 3 H 1 Y 8 H 1 Y
    1 Y 2 H 6 Y 2 H 1 H 1 Y 4 H 1 Y 3 Y 1 Y).

Definition cf177 : config := (Config 26 H 8 H 3 H 11 H 11 Y 9 H 9 H 1 Y 4 H
    1 Y 7 H 1 Y 1 Y 1 Y 3 H 5 H 5 Y 3 Y Y Y).

Definition cf178 : config := (Config 29 H 11 H 1 Y 10 H 1 Y 9 H 1 Y 7 H 2 H 9 Y
    7 H 1 Y 7 H 7 Y 6 Y 4 Y Y 1 Y Y).

Definition cf179 : config := (Config 32 H 4 H 11 H 11 H 11 Y 9 H 1 Y 8 H 1 Y
    7 H 1 Y 7 Y 6 H 6 Y 3 Y 3 Y Y 1 Y).

Definition cf180 : config := (Config 7 H 3 H 12 H 12 Y 9 H 2 H 11 Y 8 H 2 H
    10 Y 8 H 1 Y 8 Y 6 Y Y 4 Y 2 Y 3 Y Y).

Definition cf181 : config := (Config 7 29 32 H 10 H 1 H 1 Y 4 H 10 H 1 Y 4 H 9 H
    1 Y 3 H 9 Y 2 Y 3 Y 1 Y 4 Y 3 Y 2 Y Y).

Definition cf182 : config := (Config 27 H 10 H 2 H 12 Y 10 H 1 Y 9 H 1 Y 8 H 1 Y
    7 H 1 Y 7 H 7 Y Y 3 Y 3 Y Y 2 Y).

Definition cf183 : config := (Config 16 32 H 3 H 12 H 12 Y 10 H 1 Y 9 H 1 Y 8 H
    1 Y 7 H 1 Y 4 Y 3 H 6 Y 2 Y 3 Y 3 Y Y).

Definition cf184 : config := (Config 33 H 10 H 1 H 1 Y 3 H 11 Y 3 H 2 H 10 Y 3 H
    9 Y 2 Y 3 Y 6 Y 3 H 1 Y 4 Y 2 Y Y).

Definition cf185 : config := (Config 8 31 33 H 2 H 12 Y 3 H 11 Y 4 H 9 H 1 Y
    3 H 9 Y 4 H 8 H 8 Y 3 Y 4 Y 1 Y 1 Y 2 Y 1 Y).

Definition cf186 : config := (Config 14 H 2 H 12 Y 3 H 11 Y 3 H 10 Y 3 H 9 Y
    3 H 8 Y 3 H 1 Y 6 H 6 Y Y 1 Y 2 Y 1 Y).

Definition cf187 : config := (Config 25 30 33 H 11 H 1 Y 9 H 2 H 11 Y 9 H 1 Y
    8 H 1 Y 6 H 1 H 1 Y 6 Y Y Y 3 Y 1 Y Y).

Definition cf188 : config := (Config 32 H 10 H 1 H 1 Y 3 H 11 Y 3 H 10 Y 5 H 7 H
    1 H 1 Y 2 Y 3 Y 5 Y Y 3 Y 1 Y 1 Y).

Definition cf189 : config := (Config 33 H 11 H 1 Y 10 H 1 Y 9 H 1 Y 8 H 1 Y 6 H
    2 H 8 Y 7 H 7 Y 2 Y 2 Y 3 Y Y 2 Y).

Definition cf190 : config := (Config 30 H 2 H 12 Y 3 H 11 Y 4 H 9 H 1 Y 3 H
    9 Y 3 H 8 Y 2 H 1 Y 6 Y 5 Y 3 Y 1 Y 1 Y).

Definition cf191 : config := (Config 31 H 2 H 12 Y 3 H 11 Y 3 H 10 Y 3 H 9 Y
    3 H 8 Y 2 H 1 H 1 Y 5 Y 1 Y 2 Y 1 Y 1 Y).

Definition cf192 : config := (Config 27 H 11 H 1 Y 9 H 2 H 11 Y 9 H 1 Y 8 H
    1 Y 7 H 1 Y 7 H 7 Y Y Y 3 Y 2 Y 2 Y).

Definition cf193 : config := (Config 18 21 30 33 H 11 H 1 Y 4 H 10 H 1 Y 5 H
    8 H 1 H 1 Y 3 H 9 Y 2 Y 4 Y Y 4 Y 3 Y 2 Y Y).

Definition cf194 : config := (Config 6 10 19 33 H 4 H 12 H 12 H 12 Y 9 H 2 H
    11 Y 9 H 1 Y 8 H 1 Y 8 Y 5 Y 1 Y 3 Y 3 Y Y 2 Y).

Definition cf195 : config := (Config 18 H 10 H 2 H 12 Y 10 H 1 Y 8 H 2 H 10 Y 8 H
    1 Y 7 H 1 Y 5 Y 1 Y 3 Y 1 Y Y 1 Y).

Definition cf196 : config := (Config 32 H 4 H 12 H 12 H 12 Y 10 H 1 Y 9 H 1 Y
    7 H 2 H 9 Y 8 Y 5 Y 1 Y 3 Y Y 1 Y 1 Y).

Definition cf197 : config := (Config 24 H 11 H 1 Y 3 H 11 Y 3 H 10 Y 4 H 2 H
    9 Y 2 Y 6 H 7 H 7 Y Y 1 Y 3 Y Y Y).

Definition cf198 : config := (Config 33 H 11 H 1 Y 3 H 11 Y 3 H 10 Y 4 H 2 H
    9 Y 2 Y 5 H 7 Y 4 Y 3 Y 2 H 4 Y 2 Y Y).

Definition cf199 : config := (Config 21 24 30 33 H 11 H 1 Y 3 H 11 Y 3 H 10 Y
    6 H 6 H 1 H 1 H 1 Y 2 Y 4 Y 4 Y Y 3 Y 1 Y 1 Y).

Definition cf200 : config := (Config 23 H 3 H 12 H 12 Y 10 H 1 Y 7 H 3 H 10 H
    10 Y 8 H 1 Y 8 Y 5 Y 1 Y Y Y 3 Y Y).

Definition cf201 : config := (Config 1 2 32 H 11 H 1 Y 10 H 1 Y 9 H 1 Y 6 H 3 H
    9 H 9 Y 7 H 1 Y 5 Y 4 Y 1 Y 3 Y 2 Y 1 Y).

Definition cf202 : config := (Config 10 H 9 H 1 Y 8 H 1 Y 7 H 1 Y 6 H 1 Y 5 H
    1 H 2 H 6 Y H 1 Y 3 Y 1 Y 1 Y).

Definition cf203 : config := (Config 12 13 19 20 H 2 H 13 Y 3 H 12 Y 3 H 2 H
    11 Y 3 H 10 Y Y 3 H 8 H 8 Y Y Y 3 H 5 Y 3 Y Y Y).

Definition cf204 : config := (Config 36 H 11 H 1 Y 9 H 2 H 11 Y 7 H 3 H 10 H
    10 Y 7 H 1 H 1 Y 7 Y 6 Y 5 Y 1 Y 3 Y Y 2 Y).

Definition cf205 : config := (Config 35 H 3 H 12 H 12 Y 9 H 2 H 11 Y 9 H 1 Y
    8 H 9 H 9 Y 7 Y 7 Y 6 H 6 Y Y 3 Y 2 Y 1 Y).

Definition cf206 : config := (Config 36 H 11 H 1 Y 10 H 1 Y 8 H 9 H 1 Y 7 H 1 H
    1 Y 7 Y 5 H 1 H 1 Y 4 Y 1 Y Y 1 Y 1 Y).

Definition cf207 : config := (Config 18 19 25 26 H 11 H 2 H 13 Y 10 H 2 H 12 Y
    10 H 10 H 1 Y 9 H 1 Y 1 Y 8 H 1 Y 1 Y 1 Y 5 Y 4 Y Y Y).

Definition cf208 : config := (Config 35 H 4 H 12 H 12 H 12 Y 10 H 10 H 1 Y 8 H
    2 H 10 Y 9 Y 5 H 1 Y 1 Y 6 Y 4 Y 3 Y 2 Y 1 Y).

Definition cf209 : config := (Config 26 H 4 H 12 H 12 H 12 Y 10 H 1 Y 8 H 9 H
    1 Y 9 Y 6 Y 1 Y 6 H 6 H 6 Y Y Y 1 Y 1 Y).

Definition cf210 : config := (Config 35 H 11 H 1 Y 8 H 10 H 1 Y 9 H 1 Y 8 H 1 Y
    6 H 8 H 8 H 8 Y Y 1 Y 4 Y Y Y Y).

Definition cf211 : config := (Config 31 H 11 H 1 Y 8 H 3 H 11 H 11 Y 9 H 1 Y
    8 H 1 Y 5 Y 2 H 7 Y Y Y 2 H 1 Y 1 Y Y).

Definition cf212 : config := (Config 35 H 5 H 9 H 1 H 1 H 1 Y 3 H 11 Y 3 H 10 Y
    3 H 9 Y 2 H 1 Y 1 Y Y 3 Y 1 Y 1 Y 2 Y).

Definition cf213 : config := (Config 34 H 2 H 13 Y 3 H 12 Y 3 H 2 H 11 Y 3 H
    10 Y 9 H 1 Y 3 H 8 H 8 Y Y Y 3 H 5 Y 3 Y Y Y).

Definition cf214 : config := (Config 37 H 11 H 1 Y 10 H 1 Y 8 H 9 H 1 Y 9 H 9 H
    1 H 1 Y 3 H 8 H 8 Y Y Y Y 4 Y Y Y).

Definition cf215 : config := (Config 27 H 2 H 13 Y 4 H 2 H 12 Y 3 H 2 H 11 Y
    2 H 10 Y 9 H 1 Y 1 Y 1 Y 4 H 1 Y 5 H 1 Y 4 Y Y 1 Y).

Definition cf216 : config := (Config 8 9 15 16 H 2 H 13 Y 3 H 2 H 12 Y 3 H
    11 Y Y 4 H 9 H 9 H 9 Y Y Y 5 H 6 H 6 Y Y 3 Y Y Y).

Definition cf217 : config := (Config 8 9 15 16 H 12 H 1 Y 10 H 11 H 1 Y 10 H 1 Y
    1 Y 7 H 1 H 1 H 1 Y 1 Y 2 H 7 Y 4 H 1 Y 1 Y 4 Y Y Y).

Definition cf218 : config := (Config 33 H 3 H 12 H 12 Y 10 H 1 Y 9 H 1 Y 8 H
    1 Y 7 H 1 Y 7 Y 1 Y 5 H 5 Y Y Y 1 Y).

Definition cf219 : config := (Config 28 H 12 H 1 Y 11 H 1 Y 10 H 1 Y 9 H 1 Y
    8 H 1 Y 7 H 1 Y 7 H 7 Y 3 Y 4 Y Y Y 2 Y).

Definition cf220 : config := (Config 36 H 11 H 1 Y 10 H 1 Y 9 H 1 Y 8 H 1 Y 5 H
    3 H 8 H 8 Y 1 H 1 Y 5 Y 3 Y 1 Y Y 2 Y).

Definition cf221 : config := (Config 31 H 3 H 12 H 1 Y 3 H 12 Y 4 H 10 H 1 Y
    3 H 10 Y 3 H 9 Y 2 H 1 Y 1 Y 5 Y 3 Y 1 Y 2 Y Y).

Definition cf222 : config := (Config 34 H 2 H 13 Y 3 H 12 Y 5 H 9 H 1 H 1 Y
    3 H 10 Y 4 H 9 H 9 Y 3 Y 6 Y Y Y 3 Y 1 Y 1 Y).

Definition cf223 : config := (Config 37 H 12 H 1 Y 11 H 11 H 1 Y 10 H 1 Y 9 H
    1 Y 8 H 1 Y 8 H 8 Y 2 Y 5 H 6 Y 2 Y 4 Y 1 Y 2 Y).

Definition cf224 : config := (Config 36 H 12 H 1 Y 11 H 1 Y 10 H 1 Y 9 H 1 Y
    8 H 1 Y 7 H 8 H 8 Y 3 H 7 Y 2 Y 4 Y Y 3 Y Y).

Definition cf225 : config := (Config 35 H 2 H 13 Y 3 H 12 Y 3 H 11 Y 3 H 10 Y
    3 H 9 Y 3 H 8 Y 3 H 6 H 1 Y 6 Y 1 Y 2 Y 1 Y 1 Y).

Definition cf226 : config := (Config 35 37 H 12 H 1 Y 10 H 2 H 12 Y 10 H 1 Y 8 H
    2 H 10 Y 8 H 1 Y 8 H 8 Y 6 Y 5 Y 4 Y Y 2 Y 1 Y).

Definition cf227 : config := (Config 30 H 12 H 1 Y 10 H 2 H 12 Y 9 H 2 H 11 Y
    9 H 1 Y 8 H 1 Y 8 H 8 Y Y Y 4 Y 2 Y 3 Y Y).

Definition cf228 : config := (Config 35 H 11 H 2 H 13 Y 11 H 1 Y 9 H 2 H 11 Y
    9 H 1 Y 7 H 1 H 1 Y 7 Y 7 Y 4 Y 4 Y 3 Y Y 1 Y).

Definition cf229 : config := (Config 36 H 3 H 13 H 13 Y 10 H 2 H 12 Y 10 H 1 Y
    7 H 3 H 10 H 10 Y 9 Y 7 Y 3 Y 4 Y 3 Y 1 Y 2 Y Y).

Definition cf230 : config := (Config 7 H 4 H 13 H 13 H 13 Y 10 H 2 H 12 Y 9 H
    2 H 11 Y 9 H 1 Y 9 Y 6 Y 1 Y 4 Y 3 Y Y 3 Y Y).

Definition cf231 : config := (Config 19 H 10 H 1 H 1 H 1 Y 4 H 11 H 1 Y 4 H 10 H
    1 Y 3 H 10 Y 2 Y 4 Y Y 5 Y 3 Y 1 Y 2 Y Y).

Definition cf232 : config := (Config 11 33 37 H 2 H 13 Y 5 H 10 H 1 H 1 Y 3 H
    11 Y 4 H 9 H 1 Y 3 H 9 Y 6 Y 1 Y 1 Y 3 Y 1 Y Y 1 Y).

Definition cf233 : config := (Config 35 H 3 H 13 H 13 Y 11 H 1 Y 9 H 2 H 11 Y
    8 H 2 H 10 Y 9 H 9 Y 6 Y 5 Y Y 4 Y Y Y 2 Y).

Definition cf234 : config := (Config 6 H 2 H 13 Y 10 H 2 H 12 Y 7 H 4 H 11 H
    11 H 11 Y 9 H 1 Y 9 Y 6 Y Y 5 Y 3 Y Y 3 Y Y).

Definition cf235 : config := (Config 32 H 12 H 1 Y 9 H 11 H 1 Y 10 H 1 Y 9 H
    1 Y 9 Y 7 H 1 Y 7 H 1 Y 6 H 6 Y Y Y 1 Y 1 Y).

Definition cf236 : config := (Config 10 H 10 H 1 Y 9 H 1 Y 8 H 1 Y 7 H 1 Y 6 H
    1 Y 5 H 1 H 6 H 1 H 1 Y 1 Y 1 Y Y Y).

Definition cf237 : config := (Config 36 H 12 H 1 Y 11 H 9 H 3 H 12 H 12 Y 10 H
    1 Y 8 H 1 H 1 Y 8 Y 8 H 8 Y Y 5 Y 4 Y Y 3 Y Y).

Definition cf238 : config := (Config 43 H 12 H 1 Y 11 H 11 H 1 Y 7 H 4 H 11 H
    11 H 11 Y 9 H 10 Y 2 H 9 Y Y Y 3 H 1 Y 1 Y 1 Y 1 Y 2 Y).

Definition cf239 : config := (Config 36 H 4 H 11 H 1 H 1 Y 3 H 2 H 12 Y 4 H
    10 H 1 Y 5 H 1 Y 7 H 1 H 1 Y 1 Y 1 Y 1 Y 4 Y Y Y Y).

Definition cf240 : config := (Config 38 H 12 H 1 Y 11 H 1 Y 10 H 1 Y 9 H 1 Y
    8 H 1 Y 8 H 8 H 8 H 8 Y 2 H 1 Y 5 Y Y 3 Y 1 Y Y).

Definition cf241 : config := (Config 37 H 12 H 1 Y 11 H 1 Y 10 H 1 Y 9 H 1 Y
    8 H 1 Y 6 H 1 H 1 H 8 H 8 Y Y Y 2 H 1 Y 1 Y 1 Y Y).

Definition cf242 : config := (Config 14 H 9 H 1 Y 8 H 1 Y 7 H 1 Y 6 H 1 Y 5 H
    1 H 1 Y H 5 Y 4 Y 1 Y 1 Y).

Definition cf243 : config := (Config 32 H 3 H 11 H 11 Y 7 H 3 H 10 H 10 Y 7 H
    2 H 9 Y 8 Y 6 Y Y 2 Y 3 Y Y 2 Y).

Definition cf244 : config := (Config 32 H 3 H 11 H 11 Y 7 H 3 H 10 H 10 Y 7 H
    2 H 9 Y 8 Y 6 Y Y Y 3 Y 1 Y 2 Y).

Definition cf245 : config := (Config 30 H 10 H 1 Y 9 H 1 Y 8 H 8 H 1 Y 6 H 1 H
    1 Y 6 Y 5 H 1 Y 1 Y Y 3 Y Y).

Definition cf246 : config := (Config 1 2 30 H 2 H 11 Y 8 H 2 H 10 Y 8 H 7 H 2 H
    9 Y 8 Y 4 H 1 Y 1 Y Y 3 Y 1 Y 2 Y).

Definition cf247 : config := (Config 6 H 10 H 1 Y 4 H 9 H 1 Y 3 H 9 Y 4 H 1 Y
    4 Y Y 3 H 1 Y 4 H 1 Y 3 Y 1 Y).

Definition cf248 : config := (Config* 31 H 10 H 1 Y 8 H 2 H 10 Y 8 H 1 Y 5 H 1 H
    1 H 1 Y 5 Y 1 Y Y Y 3 Y Y).

Definition cf249 : config := (Config 26 H 2 H 12 Y 3 H 11 Y 6 H 2 H 10 Y 2 H
    1 Y 3 H 8 Y Y 1 Y 3 H 5 H 5 Y 3 Y Y Y).

Definition cf250 : config := (Config 20 H 8 H 1 H 1 H 1 Y 3 H 10 Y 3 H 9 Y 3 H
    8 Y 2 Y 4 Y 5 H 1 Y 1 Y Y 2 Y).

Definition cf251 : config := (Config 18 H 10 H 1 Y 9 H 1 Y 8 H 1 Y 7 H 1 Y 6 H
    1 Y 3 Y 3 H 1 Y H 4 Y Y 1 Y).

Definition cf252 : config := (Config 18 H 11 H 1 Y 10 H 1 Y 9 H 1 Y 8 H 1 Y 7 H
    1 Y 7 H 7 H 7 Y 3 Y Y 3 Y 1 Y 1 Y).

Definition cf253 : config := (Config 33 H 3 H 12 H 12 Y 9 H 2 H 11 Y 9 H 1 Y
    7 H 2 H 9 Y 8 Y 6 Y Y 5 Y 4 Y Y Y).

Definition cf254 : config := (Config 11 12 33 H 3 H 12 H 12 Y 8 H 3 H 11 H
    11 Y 9 H 1 Y 8 H 1 Y 8 Y 6 Y Y Y 3 Y 1 Y 2 Y).

Definition cf255 : config := (Config 33 H 10 H 2 H 12 Y 10 H 1 Y 9 H 1 Y 8 H 1 Y
    7 H 1 Y 7 H 7 Y Y 2 Y 3 Y 3 Y Y).

Definition cf256 : config := (Config 31 H 11 H 1 Y 9 H 2 H 11 Y 9 H 1 Y 8 H
    1 Y 7 H 1 Y 7 H 7 Y Y Y 2 Y 2 Y 2 Y).

Definition cf257 : config := (Config 33 H 10 H 2 H 12 Y 10 H 1 Y 9 H 1 Y 8 H 1 Y
    6 H 1 H 1 Y 6 Y 3 Y Y 3 Y 1 Y 1 Y).

Definition cf258 : config := (Config 24 H 3 H 11 H 11 Y 9 H 1 Y 7 H 2 H 9 Y
    7 H 1 Y 7 Y 5 Y 5 H 5 Y 2 Y Y 2 Y).

Definition cf259 : config := (Config 4 5 22 29 H 2 H 12 Y 3 H 11 Y 4 H 9 H 1 Y
    3 H 9 Y 4 H 8 H 8 Y 3 Y 5 Y 1 Y 3 Y Y 1 Y).

Definition cf260 : config := (Config 31 H 3 H 12 H 12 Y 10 H 1 Y 9 H 1 Y 8 H
    8 H 1 Y 8 Y 6 Y 5 H 1 Y 1 Y Y 3 Y Y).

Definition cf261 : config := (Config 15 16 33 H 10 H 2 H 12 Y 10 H 1 Y 9 H 1 Y
    8 H 1 Y 7 H 1 Y 4 Y 1 Y 2 H 1 Y 1 Y Y Y).

Definition cf262 : config := (Config 33 H 11 H 1 Y 4 H 10 H 1 Y 3 H 10 Y 3 H 2 H
    9 Y 2 Y 4 Y Y 4 Y 4 H 1 Y 3 Y 1 Y).

Definition cf263 : config := (Config 21 26 33 H 11 H 1 Y 4 H 10 H 1 Y 3 H 10 Y
    5 H 7 H 1 H 1 Y 2 Y 4 Y Y 4 Y Y 3 Y 1 Y).

Definition cf264 : config := (Config* 5 30 H 2 H 12 Y 3 H 11 Y 3 H 10 Y 3 H 9 Y
    5 H 8 H 8 H 8 Y 4 Y Y 4 Y 1 Y 2 Y 1 Y).

Definition cf265 : config := (Config 14 29 31 H 4 H 12 H 12 H 12 Y 10 H 1 Y 8 H
    2 H 10 Y 8 H 1 Y 8 Y 5 Y 1 Y Y Y 3 Y Y).

Definition cf266 : config := (Config 1 2 32 H 11 H 1 Y 3 H 11 Y 3 H 10 Y 3 H
    9 Y 4 H 1 Y 4 Y 3 H 1 Y 5 H 1 Y 3 Y 1 Y 1 Y).

Definition cf267 : config := (Config 35 H 9 H 3 H 12 H 12 Y 9 H 2 H 11 Y 9 H
    1 Y 7 H 1 H 1 Y 7 Y Y Y 3 Y 1 Y 1 Y 2 Y).

Definition cf268 : config := (Config 32 H 2 H 12 Y 5 H 9 H 1 H 1 Y 3 H 10 Y 3 H
    9 Y 3 H 1 Y 1 Y 1 Y 5 H 5 Y 2 Y Y 2 Y).

Definition cf269 : config := (Config 33 H 10 H 1 H 1 Y 3 H 11 Y 3 H 10 Y 5 H 1 Y
    3 Y 5 H 7 H 7 H 7 Y Y 1 Y 3 Y Y Y).

Definition cf270 : config := (Config 33 H 12 H 1 Y 11 H 1 Y 9 H 10 H 1 Y 9 H
    1 Y 9 H 9 H 9 Y 7 H 1 Y 1 Y Y Y 4 Y Y Y).

Definition cf271 : config := (Config 18 19 33 H 3 H 11 H 1 Y 3 H 11 Y 3 H 3 H
    9 H 1 Y 3 H 9 Y 6 H 1 Y 1 Y Y 3 Y 1 Y 1 Y 2 Y).

Definition cf272 : config := (Config 31 H 11 H 1 Y 9 H 2 H 11 Y 9 H 1 Y 8 H
    1 Y 6 H 8 Y 2 H 7 Y Y Y 2 H 1 Y 1 Y Y).

Definition cf273 : config := (Config 8 H 9 H 1 H 1 H 1 Y 3 H 11 Y 6 H 7 H 1 H
    1 H 1 Y 2 Y 4 Y Y 1 Y 1 Y 3 Y Y Y).

Definition cf274 : config := (Config 36 H 2 H 12 Y 4 H 10 H 1 Y 3 H 10 Y 3 H 9 Y
    4 H 1 Y 6 H 1 H 1 Y 1 Y 1 Y 3 Y 1 Y 2 Y).

Definition cf275 : config := (Config 26 H 11 H 1 Y 8 H 10 H 1 Y 8 H 2 H 10 Y 9 Y
    5 H 8 Y Y Y 3 H 1 Y 4 H 1 Y 3 Y 1 Y).

Definition cf276 : config := (Config 6 H 11 H 1 Y 3 H 11 Y 3 H 10 Y 6 H 1 Y 5 H
    8 Y 4 H 7 H 7 H 7 Y Y 1 Y 3 Y Y Y).

Definition cf277 : config := (Config 36 H 12 H 1 Y 11 H 1 Y 10 H 10 H 1 Y 7 H
    3 H 10 H 10 H 9 H 1 Y 8 Y 1 Y 1 Y Y Y 4 Y Y Y).

Definition cf278 : config := (Config 30 H 2 H 13 Y 3 H 12 Y 5 H 2 H 11 Y 3 H
    10 H 2 H 10 Y 3 Y Y Y 1 Y 3 H 5 H 5 Y 3 Y Y Y).

Definition cf279 : config := (Config 40 H 4 H 11 H 1 H 1 Y 3 H 12 Y 3 H 2 H
    11 Y 2 H 10 Y 9 H 1 Y 1 Y 2 H 7 Y 2 Y Y 3 Y Y 2 Y).

Definition cf280 : config := (Config 39 H 2 H 13 Y 3 H 2 H 12 Y 4 H 10 H 1 Y
    5 H 1 Y 9 H 1 Y 7 H 1 H 1 Y 1 Y 1 Y 4 Y 1 Y 3 Y Y).

Definition cf281 : config := (Config 27 30 33 H 12 H 1 Y 11 H 1 Y 10 H 1 Y 9 H
    1 Y 8 H 1 Y 7 H 1 Y 7 H 7 Y 6 Y 4 Y Y 3 Y 1 Y).

Definition cf282 : config := (Config 21 H 2 H 13 Y 4 H 11 H 1 Y 3 H 11 Y 3 H
    10 Y 3 H 9 Y 2 H 8 Y 2 H 7 Y 5 Y 5 Y Y 3 Y 1 Y).

Definition cf283 : config := (Config 7 H 3 H 13 H 13 Y 10 H 2 H 12 Y 9 H 2 H
    11 Y 8 H 2 H 10 Y 9 Y 7 Y Y 3 Y 2 Y 2 Y 3 Y 2 Y).

Definition cf284 : config := (Config 36 H 10 H 3 H 13 H 13 Y 11 H 1 Y 10 H 1 Y
    9 H 1 Y 7 H 1 H 1 Y 7 Y Y Y 3 Y 1 Y 1 Y 2 Y).

Definition cf285 : config := (Config 21 H 2 H 12 Y 4 H 10 H 1 Y 3 H 10 Y 3 H 9 Y
    4 H 8 H 8 Y 3 Y 1 Y 5 H 5 Y 2 Y Y 2 Y).

Definition cf286 : config := (Config 31 H 2 H 13 Y 3 H 12 Y 4 H 10 H 1 Y 3 H
    10 Y 3 H 9 Y 3 H 1 Y 7 H 7 Y 3 Y 1 Y Y Y 2 Y).

Definition cf287 : config := (Config 28 33 37 H 12 H 1 Y 9 H 3 H 12 H 12 Y 10 H
    1 Y 9 H 1 Y 7 H 1 H 1 Y 7 Y Y Y 3 Y 2 Y 2 Y 1 Y).

Definition cf288 : config := (Config 6 12 32 34 H 3 H 13 H 13 Y 11 H 1 Y 8 H
    3 H 11 H 11 Y 8 H 2 H 10 Y 9 Y 7 Y Y Y 3 Y 2 Y Y 2 Y).

Definition cf289 : config := (Config 37 H 12 H 1 Y 11 H 1 Y 10 H 1 Y 9 H 1 Y
    7 H 2 H 9 Y 8 H 8 H 8 Y 3 Y Y 2 Y 3 Y Y 1 Y).

Definition cf290 : config := (Config 27 H 12 H 1 Y 11 H 11 H 1 Y 10 H 1 Y 9 H
    1 Y 8 H 1 Y 8 H 8 Y 7 H 7 Y 2 Y Y 3 Y Y Y).

Definition cf291 : config := (Config 36 H 11 H 1 H 1 Y 4 H 11 H 1 Y 3 H 11 Y
    5 H 8 H 1 H 1 Y 2 Y 3 Y 2 Y 4 Y Y 3 Y 1 Y 1 Y).

Definition cf292 : config := (Config 18 19 37 H 3 H 13 H 13 Y 10 H 2 H 12 Y 10 H
    10 H 1 Y 9 H 1 Y 9 Y 7 Y 6 H 1 Y 1 Y Y 3 Y 1 Y 2 Y).

Definition cf293 : config := (Config 34 H 11 H 1 H 1 Y 3 H 12 Y 3 H 11 Y 4 H
    2 H 10 Y 2 Y 3 Y 4 H 7 H 7 Y Y 1 Y 3 Y Y Y).

Definition cf294 : config := (Config 28 34 36 H 11 H 2 H 13 Y 10 H 2 H 12 Y 10 H
    1 Y 8 H 2 H 10 Y 8 H 1 Y 3 Y Y 5 Y Y Y 3 Y 1 Y).

Definition cf295 : config := (Config 33 H 10 H 1 H 1 H 1 Y 3 H 12 Y 3 H 11 Y
    5 H 8 H 1 H 1 Y 2 Y 4 Y Y 5 Y Y 3 Y 1 Y 1 Y).

Definition cf296 : config := (Config 31 H 2 H 13 Y 3 H 12 Y 3 H 11 Y 4 H 9 H
    1 Y 2 H 1 H 1 H 1 Y 6 Y 1 Y 1 Y 3 Y 3 Y Y 2 Y).

Definition cf297 : config := (Config 8 9 30 37 H 2 H 13 Y 3 H 12 Y 4 H 10 H 1 Y
    3 H 10 Y 4 H 8 H 1 Y 7 Y 1 Y 1 Y 2 H 1 Y 1 Y Y Y).

Definition cf298 : config := (Config 26 33 35 H 2 H 13 Y 3 H 12 Y 5 H 9 H 1 H
    1 Y 3 H 10 Y 2 H 1 H 1 Y 6 Y 1 Y 1 Y Y Y 3 Y Y).

Definition cf299 : config := (Config 13 31 37 H 12 H 1 Y 11 H 1 Y 9 H 2 H 11 Y
    9 H 1 Y 8 H 1 Y 5 Y 2 H 7 Y Y Y 2 H 1 Y 1 Y Y).

Definition cf300 : config := (Config 35 H 2 H 13 Y 4 H 11 H 1 Y 3 H 2 H 11 Y
    3 H 10 Y 2 H 1 Y 7 Y 7 H 7 Y 3 Y Y Y 3 Y Y).

Definition cf301 : config := (Config 17 H 12 H 1 Y 8 H 4 H 12 H 12 H 12 Y 9 H
    2 H 11 Y 9 H 1 Y 9 Y 4 Y Y 4 Y Y 3 Y 1 Y 1 Y).

Definition cf302 : config := (Config 18 19 37 H 2 H 13 Y 3 H 12 Y 5 H 9 H 1 H
    1 Y 3 H 10 Y 3 H 9 Y 2 H 8 Y Y 1 Y 3 Y 1 Y Y 1 Y).

Definition cf303 : config := (Config* 24 29 37 H 12 H 1 Y 3 H 12 Y 3 H 11 Y
    7 H 6 H 1 H 1 H 1 H 1 Y 2 Y 4 Y 1 Y 4 Y Y 3 Y 1 Y 1 Y).

Definition cf304 : config := (Config* 32 H 12 H 1 Y 3 H 12 Y 3 H 11 Y 3 H 10 Y
    3 H 2 H 9 Y 2 Y Y 4 Y 1 H 5 Y 1 H 1 Y 1 Y Y).

Definition cf305 : config := (Config 37 H 2 H 13 Y 3 H 12 Y 5 H 2 H 11 Y 4 H
    10 H 10 Y 3 Y 5 H 8 H 8 H 8 Y Y 1 Y 4 Y Y Y Y).

Definition cf306 : config := (Config 35 H 12 H 1 Y 8 H 4 H 12 H 12 H 12 Y 10 H
    1 Y 9 H 1 Y 6 Y Y 2 H 7 Y Y Y 2 H 1 Y 1 Y Y).

Definition cf307 : config := (Config 36 H 2 H 13 Y 4 H 2 H 12 Y 3 H 11 Y 5 H
    10 H 10 H 10 H 1 H 1 Y 2 Y Y Y 1 Y 2 H 5 Y 3 Y Y Y).

Definition cf308 : config := (Config 7 H 5 H 13 H 13 H 13 H 13 Y 11 H 1 Y 9 H
    2 H 11 Y 9 H 1 Y 9 Y 7 H 8 Y Y 1 Y 4 Y Y Y Y).

Definition cf309 : config := (Config 30 H 2 H 13 Y 3 H 12 Y 3 H 11 Y 3 H 10 Y
    3 H 9 Y 2 H 1 H 1 H 8 H 8 Y Y 1 Y 3 Y 3 Y Y 2 Y).

Definition cf310 : config := (Config 7 H 3 H 13 H 13 Y 9 H 3 H 12 H 12 Y 9 H
    2 H 11 Y 9 H 1 Y 9 Y 6 H 8 Y 2 Y Y 4 Y Y Y Y).

Definition cf311 : config := (Config 34 H 2 H 13 Y 3 H 12 Y 3 H 11 Y 3 H 10 Y
    5 H 7 H 1 H 1 Y H 8 Y 3 H 7 Y Y 3 Y 3 Y Y 2 Y).

Definition cf312 : config := (Config 31 H 12 H 1 Y 3 H 12 Y 3 H 11 Y 5 H 2 H
    10 Y 2 Y 5 H 8 Y 2 H 1 H 7 H 7 Y Y 1 Y 3 Y Y Y).

Definition cf313 : config := (Config 42 H 2 H 13 Y 3 H 12 Y 3 H 11 Y 3 H 10 Y
    6 H 1 Y 5 H 1 H 1 H 1 H 1 Y 7 H 7 Y Y 3 Y Y 3 Y Y).

Definition cf314 : config := (Config 33 H 2 H 13 Y 3 H 12 Y 5 H 9 H 1 H 1 Y
    3 H 10 Y 4 H 9 H 9 H 1 H 1 Y 1 Y Y 5 Y Y 3 Y 1 Y 1 Y).

Definition cf315 : config := (Config 42 H 12 H 1 Y 11 H 1 Y 10 H 1 Y 9 H 1 Y
    8 H 9 H 9 H 9 H 2 H 9 Y 3 H 8 Y Y 6 Y 4 Y 3 Y 2 Y Y).

Definition cf316 : config := (Config 6 H 12 H 1 Y 3 H 12 Y 3 H 11 Y 7 H 1 Y
    5 H 9 Y 5 H 8 H 8 H 8 H 8 Y 2 H 1 Y 2 Y 3 Y 1 Y 2 Y Y).

Definition cf317 : config := (Config 46 H 12 H 1 Y 11 H 1 Y 10 H 1 Y 9 H 1 Y
    5 H 1 H 1 H 1 H 1 H 9 H 9 Y 8 H 1 Y 1 Y 2 Y 4 Y Y 3 Y 2 Y).

Definition cf318 : config := (Config 37 H 3 H 13 H 13 Y 10 H 2 H 12 Y 10 H 1 Y
    7 H 3 H 10 H 10 Y 9 Y 7 Y Y 6 Y 4 Y 1 Y 2 Y 1 Y).

Definition cf319 : config := (Config 35 H 12 H 1 Y 11 H 1 Y 10 H 10 H 1 Y 9 H
    1 Y 8 H 1 Y 8 H 8 Y 6 H 1 Y 1 Y Y 2 Y 2 Y 2 Y).

Definition cf320 : config := (Config 14 32 34 H 4 H 13 H 13 H 13 Y 11 H 1 Y
    9 H 2 H 11 Y 8 H 2 H 10 Y 9 Y 6 Y 1 Y Y Y 3 Y 1 Y 2 Y).

Definition cf321 : config := (Config 1 2 35 H 2 H 13 Y 11 H 1 Y 10 H 1 Y 8 H
    8 H 2 H 10 Y 9 Y 5 H 1 Y 7 H 1 Y 1 Y Y 3 Y 1 Y 2 Y).

Definition cf322 : config := (Config 32 H 12 H 1 Y 11 H 1 Y 10 H 1 Y 9 H 1 Y
    8 H 1 Y 8 H 8 H 8 H 8 Y 2 H 1 Y 1 Y Y 3 Y 1 Y 1 Y).

Definition cf323 : config := (Config 30 H 12 H 1 Y 9 H 3 H 12 H 12 Y 10 H 1 Y
    9 H 1 Y 8 H 1 Y 8 H 8 Y 7 H 7 Y 2 Y Y 3 Y Y Y).

Definition cf324 : config := (Config* 6 H 2 H 8 Y 6 H 1 Y 6 H 6 H 6 H 6 Y 4 Y
    Y Y Y).

Definition cf325 : config := (Config* 21 H 7 H 2 H 9 Y 7 H 6 H 2 H 8 Y 7 H 7 Y
    Y Y Y Y Y).

Definition cf326 : config := (Config* 29 H 4 H 7 H 1 H 1 Y 4 H 1 H 1 H 1 Y 1 Y
    1 Y 1 Y 2 H 4 Y 2 Y 1 Y).

Definition cf327 : config := (Config 23 H 8 H 1 Y 3 H 8 Y 5 H 5 H 1 H 1 Y 2 Y
    3 Y 1 Y 1 Y 2 Y).

Definition cf328 : config := (Config* 0 23 H 8 H 1 Y 3 H 8 Y 4 H 6 H 1 Y 2 H
    1 Y 3 Y 1 Y 3 Y Y).

Definition cf329 : config := (Config 6 H 2 H 9 Y 7 H 1 Y 4 H 7 Y 4 H 1 Y 5 H
    1 Y 4 H 1 Y 3 Y 1 Y).

Definition cf330 : config := (Config* 14 15 21 26 H 3 H 9 H 1 Y 3 H 2 H 9 Y
    3 H 8 Y 2 H 1 Y 1 Y 1 Y 1 Y 1 Y 2 Y).

Definition cf331 : config := (Config 30 H 2 H 10 Y 4 H 4 H 7 H 1 H 1 Y 5 H 1 H
    1 Y 1 Y 1 Y 1 Y 1 Y 2 Y 1 Y).

Definition cf332 : config := (Config 30 H 9 H 1 Y 7 H 2 H 9 Y 6 H 1 H 7 H 1 Y
    7 H 1 Y 1 Y 1 Y 1 Y 1 Y 2 Y).

Definition cf333 : config := (Config 25 H 9 H 1 Y 7 H 1 H 8 H 1 Y 7 H 1 H 1 Y
    1 Y 1 Y 4 H 1 Y 4 H 1 Y 3 Y 1 Y).

Definition cf334 : config := (Config* 24 H 9 H 1 Y 3 H 9 Y 3 H 8 Y 4 H 6 H 1 Y
    2 Y 3 Y 1 Y 1 Y 2 Y).

Definition cf335 : config := (Config 6 H 2 H 10 Y 8 H 1 Y 4 H 4 H 8 H 8 H 8 Y
    7 Y 5 Y Y Y 3 Y 1 Y).

Definition cf336 : config := (Config 18 H 9 H 1 Y 7 H 2 H 9 Y 6 H 2 H 8 Y 6 H
    1 Y 5 Y Y 3 Y Y 2 Y).

Definition cf337 : config := (Config 6 H 2 H 10 Y 8 H 1 Y 6 H 2 H 8 Y 6 H 7 Y
    5 Y Y 4 H 4 Y 2 Y Y).

Definition cf338 : config := (Config 27 H 2 H 10 Y 8 H 1 Y 5 H 3 H 8 H 8 Y 7 H
    7 Y 5 Y Y 2 Y 2 Y 1 Y).

Definition cf339 : config := (Config 12 H 2 H 10 Y 4 H 8 H 1 Y 3 H 2 H 8 Y 2 Y
    5 H 1 Y 5 Y 1 Y 2 Y 2 Y).

Definition cf340 : config := (Config 6 H 2 H 10 Y 8 H 1 Y 7 H 1 Y 5 H 7 Y 5 Y
    5 H 1 Y 4 H 1 Y 3 Y 1 Y).

Definition cf341 : config := (Config* 26 H 8 H 1 H 1 Y 3 H 9 Y 5 H 6 H 1 H 1 Y
    2 Y 3 Y 1 Y 1 Y 1 Y 2 Y).

Definition cf342 : config := (Config 12 13 28 H 9 H 1 Y 8 H 1 Y 7 H 1 Y 6 H
    6 H 1 Y 5 Y 4 H 5 Y Y 1 Y 2 Y).

Definition cf343 : config := (Config* 1 2 8 9 H 2 H 11 Y 3 H 10 Y 3 H 4 H 7 H
    1 H 1 Y 6 H 1 Y 1 Y 1 Y 1 Y 1 Y 2 Y 1 Y).

Definition cf344 : config := (Config 6 H 2 H 9 Y 7 H 1 Y 4 H 7 Y 4 H 1 Y 4 H
    1 H 1 Y H 4 Y Y 1 Y).

Definition cf345 : config := (Config 25 H 10 H 1 Y 9 H 9 H 1 Y 7 H 2 H 9 Y 4 H
    8 Y Y Y Y 4 H 1 Y 3 Y 1 Y).

Definition cf346 : config := (Config 28 H 2 H 11 Y 4 H 2 H 10 Y 4 H 8 H 1 Y 5 H
    1 H 1 Y 1 Y 1 Y 1 Y 1 Y 2 Y 1 Y).

Definition cf347 : config := (Config 4 5 24 29 H 2 H 11 Y 3 H 10 Y 3 H 3 H 8 H
    1 Y 2 H 1 H 1 Y 1 Y 1 Y 1 Y 1 Y 2 Y 1 Y).

Definition cf348 : config := (Config 25 H 4 H 9 H 1 H 1 Y 3 H 2 H 10 Y 3 H 9 Y
    7 H 8 Y Y Y Y 4 H 1 Y 3 Y 1 Y).

Definition cf349 : config := (Config* 24 H 8 H 2 H 10 Y 8 H 6 H 3 H 9 H 9 Y 8 H
    8 Y Y Y Y 4 H 4 Y 2 Y Y).

Definition cf350 : config := (Config 18 H 8 H 2 H 10 Y 6 H 8 H 1 Y 8 H 8 Y Y Y
    4 H 1 H 1 Y H 4 Y Y 1 Y).

Definition cf351 : config := (Config 34 H 2 H 11 Y 3 H 2 H 10 Y 4 H 1 H 7 H 1 H
    1 Y 2 H 8 Y 2 Y Y 1 Y 1 Y 2 Y 1 Y).

Definition cf352 : config := (Config 21 H 10 H 1 Y 8 H 9 H 1 Y 8 H 9 H 2 H 9 Y
    8 H 1 Y 7 Y 1 Y Y 4 H 1 Y 3 Y 1 Y).

Definition cf353 : config := (Config 29 H 10 H 1 Y 9 H 9 H 1 Y 7 H 1 H 8 H 1 Y
    8 H 1 Y 1 Y 1 Y 5 Y 4 H 4 Y 2 Y Y).

Definition cf354 : config := (Config 11 H 10 H 1 Y 8 H 2 H 10 Y 6 H 1 H 8 H 1 Y
    8 H 1 Y 1 Y 2 H 6 Y 5 Y 3 Y Y 2 Y).

Definition cf355 : config := (Config 25 H 9 H 1 Y 7 H 1 H 8 H 1 Y 7 H 1 H 1 Y
    1 Y 1 Y 3 H 1 H 1 Y H 4 Y Y 1 Y).

Definition cf356 : config := (Config 27 H 3 H 11 H 11 Y 9 H 1 Y 7 H 2 H 9 Y
    7 H 1 Y 7 Y 5 Y Y Y 2 Y 2 Y).

Definition cf357 : config := (Config 12 13 29 H 10 H 1 Y 9 H 1 Y 8 H 1 Y 6 H
    2 H 8 Y 6 H 1 Y 5 Y 3 Y Y 3 Y Y).

Definition cf358 : config := (Config 16 17 28 H 2 H 11 Y 9 H 1 Y 8 H 1 Y 7 H
    1 Y 6 H 7 Y 5 Y 4 H 5 Y 3 Y Y Y).

Definition cf359 : config := (Config 19 H 2 H 11 Y 9 H 1 Y 8 H 1 Y 6 H 2 H 8 Y
    7 H 7 Y 5 Y 2 Y 2 Y 2 Y Y).

Definition cf360 : config := (Config 6 H 2 H 11 Y 9 H 1 Y 6 H 8 H 1 Y 8 Y 5 H
    1 Y 6 H 1 Y 5 H 1 Y 4 Y Y 1 Y).

Definition cf361 : config := (Config 26 H 10 H 1 Y 6 H 4 H 10 H 10 H 10 Y 8 H 1 Y
    7 H 1 Y 6 Y Y Y 3 Y 1 Y 1 Y).

Definition cf362 : config := (Config 28 H 2 H 11 Y 9 H 1 Y 7 H 2 H 9 Y 7 H 8 H
    8 Y 6 Y Y 5 H 5 Y Y 2 Y Y).

Definition cf363 : config := (Config 6 H 2 H 10 Y 8 H 1 Y 4 H 4 H 8 H 8 H 8 Y
    7 Y 5 Y Y 4 H 1 Y 3 Y 1 Y).

Definition cf364 : config := (Config 6 H 2 H 11 Y 9 H 1 Y 6 H 3 H 9 H 9 Y 7 H
    8 Y 6 Y Y 4 H 1 Y 4 Y 2 Y Y).

Definition cf365 : config := (Config 21 H 2 H 11 Y 9 H 1 Y 8 H 6 H 3 H 9 H 9 Y
    8 Y 5 H 1 Y 6 Y 1 Y 3 Y 2 Y Y).

Definition cf366 : config := (Config 29 H 3 H 11 H 11 Y 9 H 1 Y 5 H 4 H 9 H
    9 H 9 Y 8 Y 6 Y Y Y Y 3 Y 1 Y).

Definition cf367 : config := (Config 32 H 10 H 1 Y 7 H 3 H 10 H 10 Y 8 H 1 Y 7 H
    1 Y 7 H 7 Y Y Y Y 2 Y 2 Y).

Definition cf368 : config := (Config 6 H 2 H 10 Y 8 H 1 Y 7 H 1 Y 5 H 7 Y 5 Y
    4 H 1 H 1 Y H 4 Y Y 1 Y).

Definition cf369 : config := (Config 31 H 2 H 11 Y 9 H 1 Y 8 H 1 Y 5 H 8 Y 6 Y
    5 H 1 H 5 H 1 Y 2 Y Y 3 Y 1 Y).

Definition cf370 : config := (Config 6 H 2 H 11 Y 9 H 1 Y 7 H 2 H 9 Y 6 H 8 Y
    6 Y 4 H 1 H 1 Y 1 Y Y 3 Y 1 Y).

Definition cf371 : config := (Config* 4 5 24 29 H 10 H 1 Y 9 H 1 Y 8 H 6 H 3 H
    9 H 9 Y 8 H 8 Y Y Y Y 4 H 4 Y 2 Y Y).

Definition cf372 : config := (Config 4 5 18 23 H 10 H 1 Y 9 H 1 Y 6 H 8 H 1 Y
    8 H 8 Y Y Y 4 H 1 H 1 Y H 4 Y Y 1 Y).

Definition cf373 : config := (Config 33 H 2 H 12 Y 3 H 2 H 11 Y 3 H 2 H 10 Y
    2 H 1 H 1 Y 2 H 1 Y 7 Y 1 Y 1 Y 1 Y 2 Y 1 Y).

Definition cf374 : config := (Config 30 H 11 H 1 Y 10 H 10 H 1 Y 8 H 9 H 1 Y 9 H
    9 Y 8 H 8 Y 2 Y Y Y 4 H 1 Y 3 Y 1 Y).

Definition cf375 : config := (Config 37 H 2 H 11 Y 3 H 2 H 10 Y 4 H 2 H 6 H 1 H
    2 H 9 Y 1 H 1 Y 1 Y Y 1 Y 1 Y 2 Y 1 Y).

Definition cf376 : config := (Config 21 H 10 H 1 Y 8 H 9 H 1 Y 8 H 8 H 3 H 8 H
    1 Y H 8 Y Y 1 Y Y 4 H 1 Y 3 Y 1 Y).

Definition cf377 : config := (Config 29 H 2 H 12 Y 10 H 1 Y 8 H 2 H 10 Y 8 H 8 H
    1 Y 8 Y 6 Y Y 5 H 5 Y 2 Y 3 Y 1 Y).

Definition cf378 : config := (Config 18 H 11 H 1 Y 9 H 2 H 11 Y 8 H 2 H 10 Y
    8 H 1 Y 7 H 1 Y 6 Y Y 3 Y 3 Y 3 Y 1 Y).

Definition cf379 : config := (Config 30 H 11 H 1 Y 10 H 1 Y 7 H 3 H 10 H 10 Y 8 H
    1 Y 7 H 1 Y 6 Y Y Y 3 Y 1 Y 1 Y).

Definition cf380 : config := (Config 30 33 H 3 H 12 H 12 Y 10 H 1 Y 8 H 2 H 10 Y
    7 H 2 H 9 Y 8 Y 6 Y Y Y 3 Y 2 Y Y).

Definition cf381 : config := (Config 31 H 3 H 12 H 12 Y 10 H 1 Y 9 H 1 Y 6 H
    3 H 9 H 9 Y 8 Y 6 Y Y Y Y 3 Y 1 Y).

Definition cf382 : config := (Config 25 H 2 H 12 Y 10 H 1 Y 8 H 2 H 10 Y 6 H 3 H
    9 H 9 Y 8 Y 6 Y 6 Y 4 Y 3 Y Y Y).

Definition cf383 : config := (Config 14 H 10 H 1 Y 9 H 1 Y 8 H 1 Y 7 H 1 Y 7 H
    1 Y 5 H 1 H 1 Y H 5 Y Y Y 1 Y).

Definition cf384 : config := (Config 33 H 11 H 1 Y 7 H 4 H 11 H 11 H 11 Y 9 H
    1 Y 8 H 1 Y 6 Y Y Y 2 H 1 Y 1 Y 1 Y 1 Y).

Definition cf385 : config := (Config 32 H 11 H 1 Y 7 H 4 H 11 H 11 H 11 Y 9 H
    1 Y 7 H 1 H 1 Y 7 Y Y Y Y 3 Y 1 Y 1 Y).

Definition cf386 : config := (Config 29 H 11 H 1 Y 8 H 3 H 11 H 11 Y 8 H 2 H
    10 Y 8 H 1 Y 8 H 8 Y Y Y Y 3 Y 2 Y Y).

Definition cf387 : config := (Config 6 H 2 H 11 Y 7 H 3 H 10 H 10 Y 6 H 3 H 9 H
    9 Y 8 Y 6 H 7 Y Y 1 Y 3 Y 2 Y Y).

Definition cf388 : config := (Config 6 H 2 H 11 Y 9 H 1 Y 4 H 5 H 9 H 9 H 9 H
    9 Y 8 Y 5 H 7 Y 2 Y Y 3 Y 2 Y Y).

Definition cf389 : config := (Config 18 H 2 H 11 Y 5 H 2 H 10 Y 3 H 9 Y 2 Y 5 H
    1 Y 1 Y 4 H 1 H 1 Y H 4 Y Y 1 Y).

Definition cf390 : config := (Config* 25 H 10 H 1 Y 9 H 9 H 1 Y 7 H 1 H 8 H 1 Y
    2 H 8 Y Y Y 4 H 1 H 1 Y H 4 Y Y 1 Y).

Definition cf391 : config := (Config* 36 H 2 H 11 Y 3 H 2 H 10 Y 6 H 9 H 7 H
    1 H 1 H 1 H 1 Y 1 Y Y 1 Y 1 Y 4 H 4 Y Y 1 Y).

Definition cf392 : config := (Config 27 H 10 H 1 Y 9 H 7 H 3 H 10 H 10 Y 7 H 1 H
    1 H 9 H 9 Y Y 1 Y Y Y 4 H 4 Y 2 Y Y).

Definition cf393 : config := (Config 21 H 10 H 1 Y 7 H 9 H 1 Y 7 H 1 H 1 H 9 H
    9 Y Y 1 Y Y 4 H 1 H 1 Y H 4 Y Y 1 Y).

Definition cf394 : config := (Config 16 17 32 H 2 H 13 Y 11 H 1 Y 10 H 1 Y 9 H
    1 Y 8 H 8 H 1 Y 8 Y 6 Y 5 H 6 Y 3 Y Y 3 Y 1 Y).

Definition cf395 : config := (Config 30 H 2 H 12 Y 5 H 9 H 1 H 1 Y 3 H 10 Y 3 H
    9 Y 2 H 1 Y 2 Y 1 Y 5 H 5 Y Y Y 1 Y).

Definition cf396 : config := (Config 18 H 11 H 1 Y 10 H 1 Y 9 H 1 Y 8 H 1 Y 7 H
    1 Y 7 H 1 Y 6 H 1 Y H 5 Y Y Y 1 Y).

Definition cf397 : config := (Config 34 H 11 H 1 Y 10 H 1 Y 9 H 1 Y 8 H 1 Y 7 H
    1 Y 6 H 1 H 7 H 7 Y Y Y 1 Y 1 Y 2 Y).

Definition cf398 : config := (Config 33 H 12 H 1 Y 10 H 2 H 12 Y 9 H 2 H 11 Y
    9 H 1 Y 8 H 1 Y 6 Y Y 2 H 1 Y 4 Y 3 Y 1 Y 1 Y).

Definition cf399 : config := (Config 18 H 12 H 1 Y 11 H 1 Y 10 H 9 H 2 H 11 Y
    9 H 1 Y 8 H 1 Y 5 H 1 Y 1 Y Y 3 Y 3 Y 3 Y 1 Y).

Definition cf400 : config := (Config 26 H 11 H 1 Y 10 H 10 H 1 Y 9 H 9 H 1 Y 8 H
    9 Y 2 H 8 Y Y Y 4 H 1 H 1 Y H 4 Y Y 1 Y).

Definition cf401 : config := (Config 6 H 2 H 13 Y 9 H 3 H 12 H 12 Y 10 H 1 Y
    7 H 3 H 10 H 10 Y 9 Y 7 H 8 Y 4 Y 4 Y Y 1 Y Y Y).

Definition cf402 : config := (Config 27 H 2 H 10 Y 5 H 7 H 1 H 1 Y 3 H 8 Y 3 H
    7 Y 3 Y 1 Y 1 Y 2 Y 1 Y).

Definition cf403 : config := (Config 26 H 9 H 1 Y 3 H 9 Y 4 H 2 H 8 Y 2 Y 4 H
    6 Y 2 H 5 Y 2 Y Y 2 Y).

Definition cf404 : config := (Config 0 23 H 9 H 1 Y 3 H 9 Y 4 H 7 H 1 Y 3 H
    7 Y 5 Y 1 Y 3 H 1 Y 3 Y 1 Y).

Definition cf405 : config := (Config 6 H 2 H 10 Y 8 H 1 Y 4 H 8 Y 5 H 1 Y 6 H
    1 Y 4 H 1 H 1 Y 3 Y 1 Y 1 Y).

Definition cf406 : config := (Config 21 H 8 H 3 H 11 H 11 Y 7 H 9 H 1 Y 9 H
    9 Y Y Y Y 4 H 1 H 1 Y 3 Y 1 Y 1 Y).

Definition cf407 : config := (Config 18 H 9 H 2 H 11 Y 6 H 9 H 1 Y 9 H 9 Y Y Y
    6 H 1 Y 4 H 1 H 1 Y 3 Y 1 Y 1 Y).

Definition cf408 : config := (Config 34 H 3 H 10 H 1 Y 3 H 10 Y 5 H 9 H 2 H 9 Y
    2 H 8 Y Y 6 H 1 Y 2 Y 1 Y 2 Y 1 Y).

Definition cf409 : config := (Config 25 H 10 H 1 Y 8 H 1 H 9 H 1 Y 8 H 1 H 1 Y
    1 Y 1 Y 5 H 1 Y 4 H 1 H 1 Y 3 Y 1 Y 1 Y).

Definition cf410 : config := (Config 1 2 28 H 10 H 1 Y 3 H 10 Y 5 H 7 H 1 H 1 Y
    3 H 8 Y 2 Y 3 Y 1 Y 1 Y 2 Y 1 Y).

Definition cf411 : config := (Config 27 H 2 H 11 Y 3 H 10 Y 4 H 8 H 1 Y 3 H 8 Y
    3 H 7 Y 3 Y 1 Y 1 Y 2 Y 1 Y).

Definition cf412 : config := (Config 28 H 10 H 1 Y 3 H 10 Y 3 H 9 Y 3 H 2 H 8 Y
    2 Y 3 Y 2 H 1 Y 4 Y 1 Y 2 Y).

Definition cf413 : config := (Config 25 H 2 H 11 Y 6 H 7 H 1 H 1 H 1 Y 3 H 9 Y
    3 H 8 Y 3 Y 1 Y 1 Y 2 Y 1 Y 1 Y).

Definition cf414 : config := (Config 27 H 2 H 11 Y 5 H 8 H 1 H 1 Y 3 H 9 Y 3 H
    8 Y 4 Y 1 Y 1 Y 4 H 4 Y Y 1 Y).

Definition cf415 : config := (Config 6 H 2 H 11 Y 9 H 1 Y 6 H 8 H 1 Y 8 Y 5 H
    1 Y 6 H 1 Y 5 H 1 Y 3 Y 1 Y 1 Y).

Definition cf416 : config := (Config 6 H 2 H 11 Y 9 H 1 Y 4 H 5 H 9 H 9 H 9 H
    9 Y 8 Y 6 Y Y Y 3 Y 1 Y 1 Y).

Definition cf417 : config := (Config 31 H 3 H 11 H 11 Y 6 H 4 H 10 H 10 H 10 Y
    8 H 1 Y 8 Y 6 Y Y Y 2 Y 2 Y 1 Y).

Definition cf418 : config := (Config 32 H 8 H 3 H 11 H 11 Y 9 H 1 Y 8 H 1 Y
    6 H 1 H 1 Y 6 Y Y Y 3 Y Y 2 Y).

Definition cf419 : config := (Config 29 H 10 H 1 Y 3 H 10 Y 4 H 2 H 9 Y 2 H 1 Y
    4 H 7 Y 2 H 6 Y 3 Y Y Y 2 Y).

Definition cf420 : config := (Config 32 H 10 H 1 Y 8 H 2 H 10 Y 7 H 2 H 9 Y 6 H
    2 H 8 Y 6 Y Y 4 Y Y Y 2 Y).

Definition cf421 : config := (Config 6 H 2 H 11 Y 9 H 1 Y 7 H 2 H 9 Y 6 H 8 Y
    6 Y Y 4 H 5 Y 2 H 4 Y 2 Y Y).

Definition cf422 : config := (Config 31 H 10 H 1 Y 7 H 3 H 10 H 10 Y 7 H 2 H 9 Y
    7 H 1 Y 6 Y Y 3 Y Y 2 Y 1 Y).

Definition cf423 : config := (Config 26 H 2 H 11 Y 4 H 9 H 1 Y 3 H 9 Y 3 H 2 H
    8 Y 3 Y 1 Y 3 H 1 Y 1 Y 3 Y 1 Y).

Definition cf424 : config := (Config 26 H 9 H 1 Y 3 H 9 Y 4 H 7 H 1 Y 2 H 1 H
    1 Y 3 Y 1 Y 2 H 1 Y 1 Y Y).

Definition cf425 : config := (Config 26 H 2 H 10 Y 4 H 8 H 1 Y 3 H 8 Y 4 H 6 H
    1 Y 3 Y 1 Y 4 H 4 Y Y 1 Y).

Definition cf426 : config := (Config 30 H 10 H 1 Y 3 H 10 Y 5 H 7 H 1 H 1 Y 3 H
    8 Y 5 Y 1 Y 4 H 1 Y 3 Y 1 Y 1 Y).

Definition cf427 : config := (Config 28 H 9 H 1 Y 3 H 9 Y 4 H 2 H 8 Y 2 Y 5 H
    6 H 6 Y 1 H 1 Y 1 Y Y 2 Y).

Definition cf428 : config := (Config 19 H 2 H 11 Y 3 H 2 H 10 Y 4 H 8 H 1 Y 3 H
    8 Y 4 H 7 Y 2 Y Y 3 Y 1 Y Y).

Definition cf429 : config := (Config 27 H 10 H 1 Y 3 H 10 Y 3 H 2 H 9 Y 3 H 1 Y
    4 H 7 Y 2 Y Y 2 H 1 Y 1 Y Y).

Definition cf430 : config := (Config 6 H 2 H 11 Y 9 H 1 Y 8 H 1 Y 5 H 8 Y 6 Y
    6 H 1 Y 4 H 1 H 1 Y 3 Y 1 Y 1 Y).

Definition cf431 : config := (Config 30 H 2 H 11 Y 5 H 8 H 1 H 1 Y 3 H 9 Y 4 H
    8 H 8 Y 3 Y 1 Y 1 Y 1 Y 2 Y 1 Y).

Definition cf432 : config := (Config 31 H 10 H 1 Y 8 H 2 H 10 Y 8 H 1 Y 7 H 7 H
    1 Y 6 Y 4 H 6 Y Y 1 Y 2 Y 1 Y).

Definition cf433 : config := (Config 6 H 10 H 1 Y 3 H 10 Y 3 H 9 Y 3 H 8 Y 3 H
    1 Y 3 Y 4 H 1 Y H 4 Y Y 1 Y).

Definition cf434 : config := (Config 1 2 9 22 H 2 H 11 Y 3 H 10 Y 3 H 9 Y 4 H
    2 H 8 Y 3 Y 3 H 1 H 1 Y 1 Y Y 3 Y 1 Y).

Definition cf435 : config := (Config 11 12 30 H 9 H 2 H 11 Y 9 H 9 H 1 Y 8 H
    1 Y 7 H 1 Y 4 H 1 Y 1 Y Y 3 Y Y 2 Y).

Definition cf436 : config := (Config 22 H 10 H 2 H 12 Y 8 H 10 H 1 Y 9 H 1 Y 9 H
    9 Y Y Y 6 H 1 Y 5 H 1 Y 3 Y 1 Y 1 Y).

Definition cf437 : config := (Config 28 H 10 H 2 H 12 Y 10 H 8 H 3 H 11 H 11 Y
    9 H 1 Y 9 H 9 Y Y Y Y Y 3 Y 1 Y 1 Y).

Definition cf438 : config := (Config 25 H 11 H 1 Y 10 H 10 H 1 Y 8 H 2 H 10 Y 4 H
    9 Y Y Y Y 4 H 1 H 1 Y 3 Y 1 Y 1 Y).

Definition cf439 : config := (Config 35 H 3 H 11 H 1 Y 3 H 11 Y 5 H 2 H 10 Y
    9 H 1 Y 2 H 8 Y Y 6 H 1 Y 2 Y 1 Y 2 Y 1 Y).

Definition cf440 : config := (Config 12 28 32 35 H 10 H 2 H 12 Y 10 H 1 Y 9 H
    1 Y 7 H 1 H 8 H 1 Y 8 H 1 Y 1 Y 1 Y 5 Y 2 Y 2 Y 1 Y).

Definition cf441 : config := (Config 29 H 11 H 1 Y 10 H 1 Y 8 H 1 H 9 H 1 Y 8 H
    1 H 1 Y 1 Y 1 Y 5 H 1 Y 5 H 1 Y 3 Y 1 Y 1 Y).

Definition cf442 : config := (Config 32 H 2 H 11 Y 5 H 8 H 1 H 1 Y 4 H 9 H 2 H
    9 Y 2 H 8 Y Y Y 2 Y 2 H 1 Y 1 Y Y).

Definition cf443 : config := (Config 35 H 2 H 11 Y 3 H 10 Y 6 H 9 H 2 H 9 Y 2 H
    8 Y Y 5 H 1 H 1 Y 2 Y 4 H 4 Y Y 1 Y).

Definition cf444 : config := (Config 6 H 11 H 1 Y 3 H 11 Y 6 H 7 H 1 H 1 H 1 Y
    3 H 9 Y 2 Y 3 Y 1 Y 1 Y 2 Y 1 Y 1 Y).

Definition cf445 : config := (Config 23 H 2 H 12 Y 10 H 1 Y 6 H 4 H 10 H 10 H 10 Y
    8 H 1 Y 8 Y 6 Y Y Y 3 Y 1 Y 1 Y).

Definition cf446 : config := (Config 8 H 10 H 1 H 1 Y 5 H 9 H 1 H 1 Y 3 H 10 Y
    3 H 9 Y 2 Y 3 Y 1 Y 1 Y 3 Y 3 Y 2 Y).

Definition cf447 : config := (Config 8 9 30 32 H 11 H 1 Y 9 H 2 H 11 Y 8 H 2 H
    10 Y 8 H 1 Y 7 H 1 Y 6 Y Y 4 Y Y Y 2 Y).

Definition cf448 : config := (Config 32 H 2 H 12 Y 10 H 1 Y 8 H 2 H 10 Y 8 H 8 H
    1 Y 8 Y 6 Y Y 3 Y 2 H 1 Y 3 Y 1 Y).

Definition cf449 : config := (Config 33 H 11 H 1 Y 3 H 11 Y 5 H 8 H 1 H 1 Y
    4 H 8 H 1 Y 2 Y 3 Y 1 Y 2 Y 2 Y 3 Y 2 Y).

Definition cf450 : config := (Config 30 H 2 H 12 Y 10 H 1 Y 7 H 3 H 10 H 10 Y 8 H
    1 Y 8 H 8 Y 6 Y Y 2 Y 2 Y 1 Y 1 Y).

Definition cf451 : config := (Config 27 H 10 H 1 Y 3 H 10 Y 4 H 8 H 1 Y 4 H 7 H
    1 Y 2 Y 3 Y 1 Y 2 H 1 Y 1 Y Y).

Definition cf452 : config := (Config 0 27 H 2 H 11 Y 4 H 9 H 1 Y 3 H 9 Y 3 H
    8 Y 3 H 7 Y 3 Y 1 Y 4 H 4 Y Y 1 Y).

Definition cf453 : config := (Config 27 H 10 H 1 Y 3 H 10 Y 4 H 8 H 1 Y 3 H 8 Y
    2 H 1 Y 3 Y 1 Y 3 H 1 Y 3 Y 1 Y).

Definition cf454 : config := (Config 15 30 33 H 2 H 12 Y 3 H 11 Y 5 H 8 H 1 H
    1 Y 3 H 9 Y 3 H 8 Y 3 Y 1 Y 1 Y 2 Y 1 Y 1 Y).

Definition cf455 : config := (Config 27 H 2 H 12 Y 3 H 11 Y 4 H 9 H 1 Y 3 H
    9 Y 3 H 8 Y 4 Y 1 Y 1 Y 4 H 4 Y Y 1 Y).

Definition cf456 : config := (Config 31 H 2 H 12 Y 10 H 1 Y 9 H 1 Y 7 H 8 H 1 Y
    8 Y 6 Y 6 H 1 Y 5 H 1 Y 3 Y 1 Y 1 Y).

Definition cf457 : config := (Config 30 H 2 H 12 Y 10 H 1 Y 9 H 1 Y 5 H 4 H 9 H
    9 H 9 Y 8 Y 6 Y Y Y 3 Y 1 Y 1 Y).

Definition cf458 : config := (Config 30 H 10 H 1 H 1 Y 3 H 11 Y 4 H 9 H 1 Y 3 H
    9 Y 2 H 1 Y 3 Y 1 Y 1 Y 4 Y 3 Y 1 Y).

Definition cf459 : config := (Config 31 H 10 H 1 H 1 Y 3 H 11 Y 5 H 8 H 1 H 1 Y
    3 H 9 Y 2 Y 3 Y 1 Y 1 Y 1 Y 2 Y 1 Y).

Definition cf460 : config := (Config 16 17 32 H 2 H 12 Y 10 H 1 Y 9 H 1 Y 8 H
    1 Y 6 H 8 Y 6 Y 4 H 6 Y 2 H 5 Y 3 Y Y Y).

Definition cf461 : config := (Config 31 H 2 H 12 Y 3 H 11 Y 4 H 9 H 1 Y 3 H
    9 Y 4 H 8 H 8 Y 3 Y 1 Y 1 Y 1 Y 2 Y 1 Y).

Definition cf462 : config := (Config 16 17 32 H 2 H 11 Y 9 H 1 Y 8 H 1 Y 7 H
    1 Y 7 H 7 H 7 Y 5 Y 4 H 5 Y Y 1 Y 2 Y).

Definition cf463 : config := (Config 12 13 32 H 10 H 1 Y 9 H 1 Y 8 H 1 Y 7 H
    1 Y 5 H 2 H 7 Y 5 Y 2 H 1 Y 1 Y Y 2 Y).

Definition cf464 : config := (Config 1 2 32 H 11 H 1 Y 3 H 11 Y 4 H 9 H 1 Y
    3 H 2 H 9 Y 2 Y 3 Y 3 H 6 Y Y 1 Y 2 Y 1 Y).

Definition cf465 : config := (Config 26 H 10 H 1 Y 3 H 10 Y 5 H 7 H 1 H 1 Y 3 H
    8 Y 2 Y 3 Y 2 H 5 Y 2 Y Y 2 Y).

Definition cf466 : config := (Config 23 H 2 H 12 Y 4 H 10 H 1 Y 3 H 10 Y 4 H 8 H
    1 Y 3 H 8 Y 3 Y 5 Y 1 Y 3 Y Y 2 Y).

Definition cf467 : config := (Config 32 H 2 H 12 Y 10 H 1 Y 8 H 2 H 10 Y 8 H 1 Y
    7 H 8 Y 6 Y 4 H 6 Y Y 1 Y 2 Y 1 Y).

Definition cf468 : config := (Config 33 H 11 H 1 Y 3 H 11 Y 3 H 10 Y 3 H 9 Y
    4 H 1 Y 3 Y 4 H 6 H 6 Y 3 Y 1 Y Y Y).

Definition cf469 : config := (Config 1 2 13 23 H 11 H 1 Y 3 H 11 Y 3 H 10 Y 3 H
    9 Y 4 H 1 Y 3 Y 3 H 1 H 1 Y 1 Y Y 3 Y 1 Y).

Definition cf470 : config := (Config 11 12 33 H 10 H 2 H 12 Y 9 H 2 H 11 Y 9 H
    1 Y 8 H 1 Y 7 H 1 Y 5 Y 1 Y 3 Y Y 3 Y Y).

Definition cf471 : config := (Config 19 20 33 H 11 H 1 Y 4 H 10 H 1 Y 3 H 10 Y
    3 H 9 Y 3 H 1 Y 4 Y Y 3 H 1 Y 1 Y Y Y).

Definition cf472 : config := (Config 33 H 2 H 12 Y 5 H 9 H 1 H 1 Y 3 H 10 Y 2 H
    1 H 1 H 1 Y 6 Y 1 Y 1 Y 3 Y Y 1 Y 1 Y).

Definition cf473 : config := (Config 18 H 11 H 1 Y 7 H 10 H 1 Y 9 H 1 Y 9 Y 7 H
    8 H 8 H 8 H 8 Y Y 1 Y 4 Y Y Y Y).

Definition cf474 : config := (Config 21 H 2 H 12 Y 10 H 1 Y 9 H 6 H 4 H 10 H 10 H
    10 Y 9 Y 6 H 1 Y 7 Y 1 Y 3 Y 1 Y 2 Y Y).

Definition cf475 : config := (Config 8 33 36 H 9 H 3 H 12 H 12 Y 10 H 1 Y 9 H
    9 H 1 Y 8 H 1 Y 3 H 8 Y 3 Y Y Y 3 Y 1 Y Y).

Definition cf476 : config := (Config 33 H 3 H 12 H 12 Y 10 H 1 Y 5 H 5 H 10 H
    10 H 10 H 10 Y 9 Y 7 Y Y Y Y 3 Y 1 Y 1 Y).

Definition cf477 : config := (Config 33 36 H 11 H 1 Y 9 H 2 H 11 Y 9 H 1 Y 8 H
    7 H 1 H 1 Y 7 Y 4 H 7 Y Y 1 Y 2 Y 2 Y Y).

Definition cf478 : config := (Config 30 32 36 H 2 H 12 Y 4 H 10 H 1 Y 3 H 10 Y
    4 H 9 H 9 Y 8 Y 5 H 7 H 7 Y Y 1 Y 2 Y 1 Y 1 Y).

Definition cf479 : config := (Config 15 16 33 H 11 H 1 Y 4 H 10 H 1 Y 3 H 3 H
    9 H 1 Y 2 H 1 Y 5 H 8 Y Y 1 Y 3 Y 1 Y 3 Y 2 Y).

Definition cf480 : config := (Config 20 24 36 H 2 H 12 Y 9 H 2 H 11 Y 9 H 7 H
    3 H 10 H 10 Y 9 Y 5 H 1 Y 1 Y Y 3 Y 1 Y 2 Y Y).

Definition cf481 : config := (Config 35 H 11 H 1 Y 10 H 1 Y 9 H 1 Y 5 H 1 H 1 H
    1 H 1 Y 5 H 1 Y 1 Y Y 3 Y Y 3 Y Y).

Definition cf482 : config := (Config 30 H 10 H 1 Y 5 H 8 H 1 H 1 Y 3 H 9 Y 3 H
    1 Y 3 H 1 Y 1 Y Y 2 H 1 Y 1 Y Y).

Definition cf483 : config := (Config 32 H 9 H 1 H 1 H 1 Y 3 H 11 Y 6 H 7 H 1 H
    1 H 1 Y 2 Y 4 Y Y 5 Y 1 Y Y Y Y).

Definition cf484 : config := (Config 23 H 10 H 1 Y 8 H 9 H 1 Y 7 H 2 H 9 Y 8 Y
    3 Y Y 3 H 5 H 1 H 1 Y 1 Y Y Y).

Definition cf485 : config := (Config 30 H 8 H 3 H 11 H 11 Y 9 H 9 H 1 Y 8 H
    1 Y 8 Y 4 H 7 Y Y 1 Y 2 H 1 Y 1 Y Y).

Definition cf486 : config := (Config 36 H 11 H 2 H 13 Y 8 H 11 H 1 Y 10 H 1 Y
    10 H 10 Y Y Y 6 H 1 H 1 Y 5 H 1 Y 1 Y 3 Y 1 Y 1 Y).

Definition cf487 : config := (Config 36 H 9 H 4 H 13 H 13 H 13 Y 11 H 1 Y 10 H
    10 H 1 Y 10 H 1 Y 9 H 1 Y 1 Y 1 Y 6 Y Y 3 Y 1 Y 1 Y).

Definition cf488 : config := (Config 10 11 40 H 10 H 3 H 13 H 13 Y 11 H 1 Y 10 H
    1 Y 8 H 1 H 9 H 1 Y 9 H 1 Y 1 Y 1 Y 6 Y Y 3 Y 1 Y 1 Y).

Definition cf489 : config := (Config 8 31 35 37 H 11 H 2 H 13 Y 11 H 1 Y 9 H
    2 H 11 Y 8 H 1 H 9 H 1 Y 9 H 1 Y 1 Y 1 Y 6 Y 2 Y 2 Y 1 Y 1 Y).

Definition cf490 : config := (Config 19 H 2 H 13 Y 4 H 2 H 12 Y 4 H 10 H 1 Y
    4 H 1 Y 8 H 1 H 1 Y 1 Y 2 H 7 Y 2 Y Y 3 Y 1 Y Y).

Definition cf491 : config := (Config 6 H 2 H 11 Y 9 H 1 Y 8 H 1 Y 5 H 8 Y 4 H
    2 H 7 Y H 1 Y 4 H 5 Y 3 H 4 Y Y 1 Y).

Definition cf492 : config := (Config 34 H 9 H 1 H 1 H 1 Y 3 H 11 Y 3 H 10 Y 3 H
    9 Y 2 H 1 Y 2 H 1 Y 4 Y 1 Y 3 Y 1 Y Y).

Definition cf493 : config := (Config 26 27 37 H 10 H 3 H 13 H 13 Y 11 H 1 Y 10 H
    1 Y 9 H 1 Y 8 H 1 Y 8 H 8 Y Y Y 4 Y 2 Y 3 Y Y).

Definition cf494 : config := (Config 37 H 2 H 13 Y 3 H 12 Y 3 H 11 Y 5 H 8 H
    1 H 1 Y 3 H 9 Y 2 H 8 Y 2 Y 3 Y 1 Y 2 Y Y 2 Y).

Definition cf495 : config := (Config 37 H 12 H 1 Y 11 H 1 Y 10 H 1 Y 9 H 1 Y
    6 H 3 H 9 H 9 Y 8 H 8 Y 2 Y 3 Y Y 3 Y Y 2 Y).

Definition cf496 : config := (Config 35 H 2 H 13 Y 3 H 12 Y 3 H 11 Y 3 H 10 Y
    3 H 9 Y 2 H 1 H 1 H 1 Y 5 Y 1 Y 1 Y 2 Y 1 Y 1 Y).

Definition cf497 : config := (Config 8 H 11 H 1 H 1 Y 5 H 10 H 1 H 1 Y 4 H 10 H
    1 Y 3 H 10 Y 2 Y 3 Y 1 Y 1 Y 3 Y 4 Y 2 Y 1 Y).

Definition cf498 : config := (Config 29 34 36 H 3 H 12 H 1 Y 3 H 12 Y 3 H 11 Y
    3 H 10 Y 4 H 8 H 1 Y 2 H 1 Y 1 Y 6 Y 5 Y 3 Y 1 Y 2 Y).

Definition cf499 : config := (Config 36 H 11 H 1 H 1 Y 5 H 10 H 1 H 1 Y 3 H
    11 Y 4 H 9 H 1 Y 2 Y 3 Y 1 Y 6 Y 3 Y 3 Y 3 Y 1 Y).

Definition cf500 : config := (Config 34 37 H 12 H 1 Y 11 H 1 Y 9 H 2 H 11 Y
    9 H 1 Y 8 H 9 H 9 Y 3 H 8 Y 3 Y Y Y 4 Y Y Y).

Definition cf501 : config := (Config 33 H 12 H 1 Y 11 H 1 Y 8 H 3 H 11 H 11 Y
    8 H 2 H 10 Y 8 H 1 Y 7 Y Y Y 3 Y 1 Y 1 Y 1 Y).

Definition cf502 : config := (Config 34 H 11 H 1 H 1 Y 3 H 12 Y 6 H 8 H 1 H
    1 H 1 Y 3 H 10 Y 2 Y 3 Y 1 Y 1 Y 1 Y 2 Y 1 Y 1 Y).

Definition cf503 : config := (Config 34 H 3 H 13 H 13 Y 11 H 1 Y 7 H 4 H 11 H
    11 H 11 Y 9 H 1 Y 9 Y 7 Y Y Y Y 3 Y 1 Y 1 Y).

Definition cf504 : config := (Config 35 H 11 H 1 H 1 Y 3 H 12 Y 3 H 11 Y 3 H
    3 H 9 H 1 Y 2 Y 3 Y 3 H 1 Y 5 Y 1 Y 1 Y 2 Y 1 Y).

Definition cf505 : config := (Config 8 H 11 H 1 H 1 Y 4 H 11 H 1 Y 3 H 2 H
    11 Y 3 H 10 Y 2 Y 3 Y 3 H 7 Y Y 1 Y 3 Y 3 Y 2 Y).

Definition cf506 : config := (Config 36 H 2 H 13 Y 4 H 11 H 1 Y 3 H 11 Y 5 H
    8 H 1 H 1 Y 3 H 9 Y 3 Y 2 Y 4 Y Y 3 Y 3 Y Y).

Definition cf507 : config := (Config 37 H 11 H 1 H 1 Y 3 H 12 Y 3 H 11 Y 3 H
    3 H 9 H 1 Y 2 Y 3 Y 3 H 7 Y 4 Y 1 Y Y Y Y).

Definition cf508 : config := (Config 6 H 10 H 1 Y 3 H 10 Y 3 H 9 Y 3 H 8 Y 3 H
    1 Y 3 Y 3 H 2 H 5 Y H 1 Y 3 Y 1 Y).

Definition cf509 : config := (Config 35 H 12 H 1 Y 3 H 12 Y 4 H 10 H 1 Y 3 H
    10 Y 4 H 1 Y 3 Y 4 H 1 H 1 Y 1 Y Y 3 Y 1 Y 1 Y).

Definition cf510 : config := (Config 8 9 30 37 H 12 H 1 Y 11 H 10 H 2 H 12 Y
    10 H 1 Y 8 H 2 H 10 Y 9 Y 4 Y Y Y 3 H 1 Y 1 Y Y Y).

Definition cf511 : config := (Config 21 25 37 H 2 H 13 Y 11 H 1 Y 10 H 1 Y 9 H
    7 H 3 H 10 H 10 Y 9 Y 5 H 1 Y 1 Y Y 3 Y 1 Y 2 Y Y).

Definition cf512 : config := (Config 31 H 10 H 2 H 12 Y 10 H 1 Y 9 H 9 H 1 Y 8 H
    1 Y 8 Y 4 H 7 Y Y 1 Y 3 H 1 Y 3 Y 1 Y).

Definition cf513 : config := (Config 37 39 H 2 H 13 Y 4 H 11 H 1 Y 3 H 11 Y
    5 H 8 H 1 H 1 Y 3 H 1 Y 8 H 8 Y Y 1 Y 4 Y 4 Y 1 Y 2 Y).

Definition cf514 : config := (Config 36 H 2 H 12 Y 5 H 9 H 1 H 1 Y 5 H 8 H 1 H
    1 Y 3 H 9 Y 4 H 1 Y 7 Y 1 Y 4 Y Y 1 Y Y).

Definition cf515 : config := (Config 34 H 2 H 12 Y 3 H 11 Y 4 H 2 H 10 Y 3 H
    9 Y 6 H 1 H 8 H 8 Y Y 1 Y 1 Y 4 H 4 Y Y 1 Y).

Definition cf516 : config := (Config 37 H 12 H 1 Y 11 H 1 Y 10 H 8 H 3 H 11 H
    11 Y 2 H 10 Y 8 H 1 H 1 Y 1 Y 1 Y 1 Y 4 H 1 Y 3 Y 1 Y 1 Y).

Definition cf517 : config := (Config 37 H 12 H 1 Y 11 H 1 Y 8 H 10 H 1 Y 2 H
    1 H 10 H 10 Y 8 H 1 H 1 Y 1 Y 1 Y 1 Y 4 H 1 Y 3 Y 1 Y 1 Y).

Definition cf518 : config := (Config 25 H 11 H 1 Y 9 H 10 H 1 Y 8 H 1 H 9 H 1 Y
    2 H 9 Y Y Y 4 H 1 H 1 H 1 Y H 5 Y 4 Y 1 Y 1 Y).

Definition cf519 : config := (Config 6 H 12 H 1 Y 3 H 12 Y 7 H 7 H 1 H 1 H 1 H
    1 Y 3 H 10 Y 2 Y 4 H 1 Y 7 Y 1 Y 3 Y 4 Y 2 Y 1 Y).

Definition cf520 : config := (Config 1 2 31 H 2 H 12 Y 10 H 1 Y 7 H 3 H 10 H 10 Y
    7 H 2 H 9 Y 8 Y 6 Y Y Y 3 Y 1 Y 1 Y).

Definition cf521 : config := (Config 2 31 H 2 H 12 Y 10 H 1 Y 7 H 3 H 10 H 10 Y
    7 H 2 H 9 Y 8 Y 6 Y Y 2 Y 3 Y Y 1 Y).

Definition cf522 : config := (Config 31 H 2 H 12 Y 3 H 11 Y 3 H 10 Y 3 H 2 H
    9 Y 3 H 8 Y 3 Y 3 H 6 Y Y 1 Y 2 Y 1 Y).

Definition cf523 : config := (Config 34 H 10 H 1 Y 8 H 2 H 10 Y 8 H 1 Y 7 H 1 Y
    6 H 1 H 1 Y H 6 Y 2 Y Y 3 Y Y).

Definition cf524 : config := (Config 3 36 H 3 H 11 H 1 Y 3 H 11 Y 4 H 9 H 1 Y
    4 H 8 H 1 Y 2 H 8 Y Y 2 Y 1 Y 2 Y 1 Y 2 Y).

Definition cf525 : config := (Config 35 H 2 H 12 Y 3 H 11 Y 3 H 2 H 10 Y 5 H
    7 H 1 H 1 Y 7 Y 1 Y 6 H 6 Y 2 Y Y 3 Y Y).

Definition cf526 : config := (Config 34 H 11 H 1 Y 9 H 2 H 11 Y 9 H 1 Y 5 H
    1 H 1 H 2 H 9 Y 6 Y 1 Y Y Y 4 Y Y Y).

Definition cf527 : config := (Config 27 H 2 H 12 Y 4 H 2 H 11 Y 5 H 8 H 1 H
    1 Y 2 Y 6 Y 1 Y 1 Y 4 H 5 Y 2 H 4 Y Y 1 Y).

Definition cf528 : config := (Config 31 H 10 H 1 Y 3 H 10 Y 4 H 2 H 9 Y 2 H 1 Y
    5 H 7 H 7 Y 1 H 1 Y 2 Y Y Y 2 Y).

Definition cf529 : config := (Config* 35 H 2 H 12 Y 5 H 9 H 1 H 1 Y 3 H 10 Y
    5 H 9 H 9 H 9 Y 4 Y Y 1 Y 1 Y 1 Y 2 Y 1 Y).

Definition cf530 : config := (Config 35 H 11 H 1 Y 10 H 1 Y 8 H 2 H 10 Y 8 H 1 Y
    7 H 1 Y 7 H 1 Y H 6 Y 2 Y Y 3 Y Y).

Definition cf531 : config := (Config 34 H 3 H 13 H 13 Y 11 H 1 Y 10 H 1 Y 8 H
    9 H 1 Y 9 Y 7 Y 6 H 1 Y 6 H 1 Y 4 Y Y 1 Y 1 Y).

Definition cf532 : config := (Config 37 H 12 H 1 Y 10 H 2 H 12 Y 10 H 1 Y 9 H
    1 Y 6 H 1 H 1 H 1 Y 6 Y 1 Y Y Y 4 Y Y Y).

Definition cf533 : config := (Config 12 33 37 H 2 H 13 Y 3 H 12 Y 4 H 10 H 1 Y
    3 H 10 Y 2 H 1 H 1 H 1 Y 6 Y 1 Y 1 Y 3 Y Y 1 Y 1 Y).

Definition cf534 : config := (Config 13 20 30 H 4 H 13 H 13 H 13 Y 11 H 1 Y
    10 H 1 Y 9 H 9 H 1 Y 9 Y 6 Y 1 Y 5 H 1 Y 4 Y Y 1 Y 1 Y).

Definition cf535 : config := (Config 7 H 3 H 13 H 13 Y 9 H 3 H 12 H 12 Y 10 H
    1 Y 8 H 2 H 10 Y 9 Y 7 Y Y Y 3 Y 1 Y 2 Y Y).

Definition cf536 : config := (Config 35 H 11 H 2 H 13 Y 10 H 2 H 12 Y 10 H 1 Y
    9 H 1 Y 8 H 1 Y 8 H 8 Y Y Y Y 2 Y 2 Y 1 Y).

Definition cf537 : config := (Config 6 H 2 H 12 Y 10 H 1 Y 8 H 2 H 10 Y 6 H 3 H
    9 H 9 Y 8 Y 6 Y Y 3 Y 2 H 4 Y 2 Y Y).

Definition cf538 : config := (Config 33 H 2 H 12 Y 5 H 9 H 1 H 1 Y 3 H 10 Y 3 H
    9 Y 3 H 8 Y 3 Y 1 Y 2 Y 3 H 4 Y Y 1 Y).

Definition cf539 : config := (Config 6 H 11 H 1 Y 3 H 11 Y 5 H 8 H 1 H 1 Y 3 H
    9 Y 2 H 1 Y 3 Y 1 Y 2 Y 2 H 1 Y 3 Y 1 Y).

Definition cf540 : config := (Config 35 H 10 H 1 H 1 Y 3 H 11 Y 3 H 10 Y 5 H 7 H
    1 H 1 Y 2 Y 3 Y 3 H 1 Y 4 Y 1 Y 1 Y 2 Y).

Definition cf541 : config := (Config 37 H 12 H 1 Y 10 H 2 H 12 Y 10 H 1 Y 8 H
    2 H 10 Y 7 H 2 H 9 Y 7 Y 4 Y Y Y 3 Y 1 Y Y).

Definition cf542 : config := (Config 34 H 3 H 12 H 1 Y 3 H 12 Y 4 H 10 H 1 Y
    3 H 10 Y 4 H 9 H 9 Y 3 Y 2 Y Y 1 Y 1 Y 2 Y 1 Y).

Definition cf543 : config := (Config 34 H 12 H 1 Y 11 H 1 Y 10 H 10 H 1 Y 9 H
    1 Y 7 H 1 H 1 Y 7 Y 6 H 1 Y 1 Y Y 3 Y Y 2 Y).

Definition cf544 : config := (Config 34 H 10 H 1 H 1 H 1 Y 3 H 12 Y 5 H 9 H 1 H
    1 Y 3 H 10 Y 2 Y 4 Y Y 1 Y 1 Y 1 Y 2 Y 1 Y).

Definition cf545 : config := (Config 4 5 36 H 4 H 10 H 1 H 1 Y 3 H 11 Y 3 H 10 Y
    4 H 8 H 1 Y 2 Y 6 Y 1 Y 4 H 5 Y Y 1 Y 2 Y).

Definition cf546 : config := (Config 36 H 5 H 13 H 13 H 13 H 13 Y 11 H 1 Y 7 H
    4 H 11 H 11 H 11 Y 10 Y 6 Y 1 Y 1 Y 3 Y 1 Y Y 1 Y 1 Y).

Definition cf547 : config := (Config 34 H 12 H 1 Y 11 H 11 H 1 Y 8 H 3 H 11 H
    11 Y 8 H 2 H 10 Y 7 H 1 Y 7 Y 1 Y 1 Y 4 Y Y Y 2 Y).

Definition cf548 : config := (Config 38 H 2 H 13 Y 6 H 9 H 1 H 1 H 1 Y 3 H
    11 Y 5 H 10 H 10 H 10 Y 4 Y Y 1 Y 1 Y 1 Y 2 Y 1 Y 1 Y).

Definition cf549 : config := (Config 33 H 4 H 13 H 13 H 13 Y 11 H 1 Y 10 H 1 Y
    7 H 3 H 10 H 10 Y 9 Y 6 Y 1 Y 3 Y Y 2 H 1 Y 3 Y 1 Y).

Definition cf550 : config := (Config 38 H 2 H 13 Y 11 H 1 Y 10 H 1 Y 7 H 9 H
    1 Y 9 Y 7 Y 7 H 7 H 7 H 2 H 7 Y 2 Y Y 3 Y 1 Y 1 Y).

Definition cf551 : config := (Config 6 H 2 H 12 Y 10 H 1 Y 9 H 1 Y 8 H 1 Y 6 H
    8 Y 6 Y 4 H 1 H 1 H 1 Y H 5 Y 4 Y 1 Y 1 Y).

Definition cf552 : config := (Config 19 20 40 H 2 H 13 Y 3 H 12 Y 4 H 10 H 1 Y
    6 H 7 H 1 H 1 H 1 Y 2 Y 8 H 8 Y 7 Y 1 Y 1 Y 3 Y Y 2 Y).

Definition cf553 : config := (Config 36 H 4 H 13 H 13 H 13 Y 11 H 1 Y 6 H 5 H
    11 H 11 H 11 H 11 Y 10 Y 6 Y 1 Y 1 Y 6 H 6 Y 5 Y Y 1 Y 1 Y).

Definition cf554 : config := (Config 40 H 12 H 1 Y 11 H 1 Y 10 H 1 Y 9 H 1 Y
    5 H 1 H 3 H 9 H 9 Y 2 H 8 Y 7 H 1 Y 1 Y 2 Y 3 Y Y 1 Y).

Definition cf555 : config := (Config 37 H 12 H 1 Y 9 H 3 H 12 H 12 Y 10 H 1 Y
    9 H 1 Y 7 H 1 H 1 Y 7 Y 7 H 7 Y 2 Y Y 3 Y Y 2 Y).

Definition cf556 : config := (Config 30 H 10 H 1 Y 7 H 3 H 10 H 10 Y 8 H 1 Y 6 H
    2 H 8 Y 6 Y Y Y 4 Y Y Y).

Definition cf557 : config := (Config 10 31 H 10 H 1 Y 8 H 9 H 1 Y 8 H 1 Y 7 H
    1 Y 5 H 1 Y 6 H 1 Y 5 Y 1 Y 3 Y Y).

Definition cf558 : config := (Config 27 H 11 H 1 Y 8 H 3 H 11 H 11 Y 9 H 1 Y
    8 H 1 Y 7 H 1 Y 6 Y Y Y 4 Y Y Y).

Definition cf559 : config := (Config 32 H 2 H 12 Y 10 H 1 Y 8 H 9 H 1 Y 8 H 1 Y
    8 Y 5 H 1 Y 6 H 1 Y 4 Y 1 Y 1 Y 2 Y).

Definition cf560 : config := (Config 23 H 2 H 11 Y 9 H 1 Y 7 H 2 H 9 Y 7 H 1 Y
    3 Y Y 3 H 1 H 1 Y H 4 Y Y 1 Y).

Definition cf561 : config := (Config 29 H 10 H 1 Y 8 H 2 H 10 Y 8 H 1 Y 5 H 3 H
    8 H 8 Y 6 Y Y 2 H 1 Y 2 Y Y Y).

Definition cf562 : config := (Config* 33 H 2 H 13 Y 11 H 1 Y 10 H 1 Y 9 H 9 H
    1 Y 8 H 1 Y 8 Y 6 Y 4 Y 2 H 1 Y 4 Y 1 Y 2 Y).

Definition cf563 : config := (Config 31 H 2 H 13 Y 3 H 2 H 12 Y 3 H 11 Y 3 H
    2 H 10 Y 2 Y 7 H 1 Y 6 Y 1 Y 1 Y 4 H 4 Y Y 1 Y).

Definition cf564 : config := (Config 8 9 34 H 12 H 1 Y 11 H 1 Y 10 H 10 H 1 Y
    9 H 1 Y 7 H 1 H 1 Y 7 Y 6 H 7 Y 3 Y Y Y 3 Y Y).

Definition cf565 : config := (Config 34 H 2 H 12 Y 8 H 3 H 11 H 11 Y 9 H 1 Y
    7 H 2 H 9 Y 8 Y 6 H 7 Y Y 1 Y 4 H 4 Y Y 1 Y).

Definition cf566 : config := (Config 17 H 11 H 1 Y 9 H 2 H 11 Y 9 H 1 Y 8 H
    1 Y 8 H 1 Y 6 H 1 H 1 Y H 6 Y 5 Y Y 1 Y 1 Y).

Definition cf567 : config := (Config* 6 H 2 H 9 Y 7 H 1 Y 7 H 7 H 7 H 7 H 7 Y
    5 Y Y Y Y Y).

Definition cf568 : config := (Config* 24 H 8 H 2 H 10 Y 8 H 6 H 3 H 9 H 9 Y 8 H
    8 Y Y Y Y Y Y Y).

Definition cf569 : config := (Config* 23 H 6 H 4 H 10 H 10 H 10 Y 7 H 9 H 9 H 9 Y
    Y Y Y Y 4 H 1 Y 3 Y 1 Y).

Definition cf570 : config := (Config 27 H 9 H 1 Y 3 H 9 Y 6 H 5 H 1 H 1 H 1 Y
    2 Y 3 Y 1 Y 1 Y 1 Y 2 Y).

Definition cf571 : config := (Config 27 H 9 H 1 Y 3 H 9 Y 5 H 6 H 1 H 1 Y 2 H
    1 Y 3 Y 1 Y 1 Y 3 Y Y).

Definition cf572 : config := (Config 6 H 2 H 10 Y 8 H 1 Y 4 H 8 Y 5 H 1 Y 6 H
    1 Y 5 H 1 Y 4 H 1 Y 3 Y 1 Y).

Definition cf573 : config := (Config 24 H 7 H 4 H 11 H 11 H 11 Y 8 H 9 H 1 Y
    9 H 9 Y Y Y Y Y 4 H 1 Y 3 Y 1 Y).

Definition cf574 : config := (Config 33 H 3 H 10 H 1 Y 7 H 10 H 2 H 10 Y 2 H 9 Y
    Y 6 H 1 H 1 Y 2 Y 1 Y 2 H 1 Y 1 Y Y).

Definition cf575 : config := (Config 12 13 28 H 2 H 11 Y 9 H 1 Y 6 H 3 H 9 H
    9 Y 7 H 1 Y 7 Y 5 Y Y Y 2 Y 2 Y).

Definition cf576 : config := (Config* 27 H 10 H 1 Y 3 H 10 Y 3 H 9 Y 5 H 6 H 1 H
    1 Y 2 Y 3 Y 1 Y 1 Y 1 Y 2 Y).

Definition cf577 : config := (Config 6 H 2 H 11 Y 9 H 1 Y 4 H 5 H 9 H 9 H 9 H
    9 Y 8 Y 6 Y Y Y Y 3 Y 1 Y).

Definition cf578 : config := (Config 6 H 2 H 11 Y 9 H 1 Y 6 H 3 H 9 H 9 Y 7 H
    8 Y 6 Y Y Y 4 H 4 Y 2 Y Y).

Definition cf579 : config := (Config 30 H 2 H 11 Y 4 H 9 H 1 Y 5 H 7 H 1 H 1 Y
    3 H 8 Y 3 Y 1 Y 1 Y 1 Y 2 Y 1 Y).

Definition cf580 : config := (Config 6 H 2 H 11 Y 9 H 1 Y 7 H 2 H 9 Y 6 H 8 Y
    6 Y Y 5 H 1 Y 4 H 1 Y 3 Y 1 Y).

Definition cf581 : config := (Config* 31 H 9 H 1 H 1 Y 4 H 9 H 1 Y 4 H 8 H 1 Y
    2 H 1 Y 3 Y 1 Y 1 Y 1 Y 3 Y Y).

Definition cf582 : config := (Config 6 H 2 H 11 Y 9 H 1 Y 8 H 1 Y 5 H 8 Y 6 Y
    6 H 1 Y 5 H 1 Y 4 H 1 Y 3 Y 1 Y).

Definition cf583 : config := (Config 6 H 2 H 10 Y 8 H 1 Y 4 H 8 Y 5 H 1 Y 6 H
    1 Y 4 H 1 H 1 Y H 4 Y Y 1 Y).

Definition cf584 : config := (Config 8 9 33 H 2 H 12 Y 3 H 11 Y 4 H 9 H 1 Y
    3 H 2 H 9 Y 2 Y 6 H 1 Y 6 Y 1 Y 2 Y 3 Y Y).

Definition cf585 : config := (Config 30 H 2 H 12 Y 10 H 1 Y 9 H 1 Y 5 H 4 H 9 H
    9 H 9 Y 8 Y 6 Y Y Y Y 3 Y 1 Y).

Definition cf586 : config := (Config 30 H 3 H 12 H 12 Y 10 H 1 Y 7 H 3 H 10 H
    10 Y 8 H 1 Y 8 Y 6 Y Y Y Y 2 Y 2 Y).

Definition cf587 : config := (Config 27 H 2 H 12 Y 10 H 1 Y 9 H 1 Y 7 H 2 H 9 Y
    7 H 8 Y 6 Y Y Y 4 H 4 Y 2 Y Y).

Definition cf588 : config := (Config 24 H 2 H 12 Y 10 H 1 Y 9 H 1 Y 8 H 7 H 2 H
    9 Y 8 Y 6 Y 6 H 6 Y 2 Y Y 2 Y 2 Y).

Definition cf589 : config := (Config 16 17 31 H 11 H 1 Y 3 H 11 Y 3 H 10 Y 3 H
    9 Y 3 H 1 H 1 Y 3 Y 3 H 1 Y 4 Y 1 Y 1 Y 2 Y).

Definition cf590 : config := (Config 7 H 3 H 12 H 12 Y 7 H 4 H 11 H 11 H 11 Y
    8 H 2 H 10 Y 9 Y 7 Y Y Y Y 3 Y 2 Y Y).

Definition cf591 : config := (Config 6 H 2 H 11 Y 9 H 1 Y 7 H 2 H 9 Y 8 H 8 H
    8 H 8 Y 6 Y Y 4 H 5 Y 3 Y Y Y).

Definition cf592 : config := (Config 6 H 2 H 11 Y 9 H 1 Y 8 H 1 Y 5 H 8 Y 6 Y
    6 H 1 Y 4 H 1 H 1 Y H 4 Y Y 1 Y).

Definition cf593 : config := (Config 15 H 11 H 1 Y 10 H 1 Y 8 H 2 H 10 Y 7 H 8 H
    1 Y 7 Y 5 H 7 H 7 Y Y 1 Y 2 Y 2 Y Y).

Definition cf594 : config := (Config 6 H 2 H 12 Y 10 H 1 Y 9 H 1 Y 5 H 9 Y 3 H
    1 H 1 H 1 Y 1 Y Y Y 4 H 4 Y 2 Y Y).

Definition cf595 : config := (Config 41 H 2 H 12 Y 3 H 2 H 11 Y 4 H 1 H 8 H
    1 H 1 Y 3 H 9 H 9 Y 1 H 1 Y 1 Y Y 1 Y 1 Y 2 Y 1 Y).

Definition cf596 : config := (Config 16 17 24 H 2 H 12 Y 10 H 1 Y 9 H 1 Y 8 H
    1 Y 6 H 8 Y 6 Y Y 4 H 1 H 1 Y H 4 Y Y 1 Y).

Definition cf597 : config := (Config* 19 20 36 H 2 H 13 Y 11 H 1 Y 10 H 1 Y 9 H
    9 H 1 Y 8 H 9 Y 5 H 1 Y 1 Y Y 4 H 5 Y 3 Y Y Y).

Definition cf598 : config := (Config 31 H 2 H 11 Y 6 H 7 H 1 H 1 H 1 Y 3 H 9 Y
    3 H 8 Y 3 Y 1 Y 1 Y 1 Y 2 Y 1 Y).

Definition cf599 : config := (Config 30 H 10 H 1 Y 3 H 10 Y 5 H 2 H 9 Y 2 Y 4 H
    7 Y 2 H 6 Y 2 H 5 Y 2 Y Y 2 Y).

Definition cf600 : config := (Config 31 H 10 H 1 Y 3 H 10 Y 4 H 2 H 9 Y 2 H 1 Y
    4 H 7 Y 2 H 6 Y 2 Y Y 3 Y Y).

Definition cf601 : config := (Config 1 2 26 32 H 2 H 12 Y 10 H 1 Y 6 H 4 H 10 H
    10 H 10 Y 8 H 1 Y 8 Y 6 Y Y Y 2 Y 2 Y 1 Y).

Definition cf602 : config := (Config 31 H 11 H 1 Y 3 H 11 Y 5 H 8 H 1 H 1 Y
    3 H 9 Y 2 H 1 Y 3 Y 1 Y 1 Y 4 Y 3 Y 1 Y).

Definition cf603 : config := (Config 31 H 2 H 12 Y 3 H 11 Y 5 H 8 H 1 H 1 Y
    3 H 9 Y 3 H 8 Y 3 Y 1 Y 1 Y 1 Y 2 Y 1 Y).

Definition cf604 : config := (Config 31 H 11 H 1 Y 3 H 11 Y 3 H 10 Y 4 H 2 H
    9 Y 2 Y 3 Y 2 H 6 Y 2 H 5 Y 2 Y Y 2 Y).

Definition cf605 : config := (Config 6 H 2 H 12 Y 10 H 1 Y 7 H 3 H 10 H 10 Y 7 H
    9 Y 7 Y Y Y 4 H 5 Y 2 H 4 Y 2 Y Y).

Definition cf606 : config := (Config 30 H 2 H 11 Y 5 H 8 H 1 H 1 Y 3 H 9 Y 4 H
    7 H 1 Y 3 Y 1 Y 1 Y 4 H 4 Y Y 1 Y).

Definition cf607 : config := (Config 31 H 11 H 1 Y 3 H 11 Y 4 H 2 H 10 Y 3 H
    1 Y 4 H 8 Y 2 H 7 Y 2 Y Y 2 H 1 Y 1 Y Y).

Definition cf608 : config := (Config 35 H 2 H 12 Y 5 H 9 H 1 H 1 Y 3 H 2 H 10 Y
    3 H 9 Y 3 Y 1 Y 3 H 6 Y Y 1 Y 2 Y 1 Y).

Definition cf609 : config := (Config 27 H 11 H 1 Y 3 H 11 Y 4 H 9 H 1 Y 3 H
    9 Y 3 H 1 Y 3 Y 1 Y 4 H 1 Y H 4 Y Y 1 Y).

Definition cf610 : config := (Config 29 H 10 H 1 Y 3 H 10 Y 4 H 8 H 1 Y 2 H 1 H
    1 H 1 Y 3 Y 1 Y 5 Y 3 H 1 Y 1 Y Y).

Definition cf611 : config := (Config 23 H 10 H 1 Y 3 H 10 Y 4 H 8 H 1 Y 3 H 8 Y
    6 Y 1 Y 3 H 1 H 1 Y H 4 Y Y 1 Y).

Definition cf612 : config := (Config 23 H 11 H 1 Y 4 H 10 H 1 Y 3 H 10 Y 5 H 1 Y
    4 Y Y 2 H 1 H 1 H 1 Y 1 Y Y Y Y).

Definition cf613 : config := (Config 16 17 32 H 12 H 1 Y 3 H 12 Y 3 H 11 Y 3 H
    10 Y 3 H 2 H 9 Y 2 Y 3 Y 3 H 1 Y 4 Y 1 Y 1 Y 2 Y).

Definition cf614 : config := (Config 11 12 33 H 3 H 13 H 13 Y 10 H 2 H 12 Y 8 H
    3 H 11 H 11 Y 9 H 1 Y 9 Y 7 Y Y Y Y 2 Y 2 Y 1 Y).

Definition cf615 : config := (Config 12 13 30 36 H 2 H 13 Y 11 H 1 Y 9 H 2 H
    11 Y 8 H 2 H 10 Y 8 H 1 Y 5 Y Y 3 H 6 Y 3 Y Y Y 2 Y).

Definition cf616 : config := (Config 30 H 11 H 1 Y 3 H 11 Y 4 H 9 H 1 Y 3 H
    9 Y 2 H 1 H 1 Y 3 Y 1 Y 5 Y 4 H 1 Y 3 Y 1 Y).

Definition cf617 : config := (Config 30 H 2 H 12 Y 3 H 11 Y 4 H 9 H 1 Y 3 H
    9 Y 4 H 7 H 1 Y 3 Y 1 Y 1 Y 4 H 4 Y Y 1 Y).

Definition cf618 : config := (Config 35 H 2 H 13 Y 3 H 12 Y 5 H 9 H 1 H 1 Y
    3 H 10 Y 4 H 9 H 9 Y 3 Y 1 Y 1 Y 1 Y 1 Y 2 Y 1 Y).

Definition cf619 : config := (Config 35 H 12 H 1 Y 3 H 12 Y 4 H 10 H 1 Y 3 H
    2 H 10 Y 2 H 1 Y 3 Y 3 H 7 Y Y 1 Y 4 Y 3 Y 1 Y).

Definition cf620 : config := (Config* 31 H 12 H 1 Y 3 H 12 Y 3 H 11 Y 3 H 10 Y
    3 H 2 H 9 Y 2 Y 3 Y 2 H 6 Y 1 H 1 Y 1 Y Y 2 Y).

Definition cf621 : config := (Config 34 H 2 H 13 Y 3 H 12 Y 5 H 9 H 1 H 1 Y
    3 H 10 Y 4 H 8 H 1 Y 3 Y 1 Y 1 Y 1 Y 2 Y 1 Y 1 Y).

Definition cf622 : config := (Config* 6 H 2 H 10 Y 8 H 1 Y 8 H 8 H 8 H 8 H 8 H
    8 Y 6 Y Y Y Y Y Y).

Definition cf623 : config := (Config 31 H 10 H 1 Y 3 H 10 Y 7 H 5 H 1 H 1 H 1 H
    1 Y 2 Y 3 Y 1 Y 1 Y 1 Y 1 Y 2 Y).

Definition cf624 : config := (Config 31 H 10 H 1 Y 3 H 10 Y 6 H 6 H 1 H 1 H 1 Y
    2 H 1 Y 3 Y 1 Y 1 Y 1 Y 3 Y Y).

Definition cf625 : config := (Config 12 13 32 H 2 H 12 Y 10 H 1 Y 6 H 4 H 10 H
    10 H 10 Y 8 H 1 Y 8 Y 6 Y Y Y Y 2 Y 2 Y).

Definition cf626 : config := (Config 31 H 11 H 1 Y 3 H 11 Y 4 H 9 H 1 Y 5 H
    7 H 1 H 1 Y 2 Y 3 Y 1 Y 1 Y 1 Y 1 Y 2 Y).

Definition cf627 : config := (Config* 30 H 11 H 1 Y 3 H 11 Y 3 H 10 Y 6 H 6 H
    1 H 1 H 1 Y 2 Y 3 Y 1 Y 1 Y 1 Y 1 Y 2 Y).

Definition cf628 : config := (Config 6 H 2 H 12 Y 10 H 1 Y 6 H 4 H 10 H 10 H 10 Y
    8 H 9 Y 7 Y Y Y Y 4 H 4 Y 2 Y Y).

Definition cf629 : config := (Config 35 H 11 H 1 Y 3 H 11 Y 4 H 9 H 1 Y 3 H
    1 H 1 H 1 Y 3 Y 1 Y 2 H 1 Y 5 Y 1 Y 3 Y Y).

Definition cf630 : config := (Config 27 H 2 H 13 Y 11 H 1 Y 9 H 2 H 11 Y 9 H
    8 H 2 H 10 Y 9 Y 7 Y Y 6 H 6 Y 2 Y Y 2 Y 2 Y).

Definition cf631 : config := (Config 31 H 11 H 1 Y 3 H 11 Y 6 H 7 H 1 H 1 H
    1 Y 3 H 9 Y 5 Y 1 Y 1 Y 1 Y 3 H 1 Y 3 Y 1 Y).

Definition cf632 : config := (Config 35 H 11 H 1 Y 3 H 11 Y 5 H 2 H 10 Y 2 H
    1 Y 4 H 8 Y 2 H 7 Y 2 H 6 Y 2 Y Y 3 Y Y).

Definition cf633 : config := (Config* 6 H 2 H 11 Y 9 H 1 Y 9 H 9 H 9 H 9 H 9 H
    9 H 9 Y 7 Y Y Y Y Y Y Y).

Definition the_configs : configseq := 
  (Seq cf001 cf002 cf003 cf004 cf005 cf006 cf007 cf008 cf009 cf010 cf011
       cf012 cf013 cf014 cf015 cf016 cf017 cf018 cf019 cf020 cf021 cf022 cf023
       cf024 cf025 cf026 cf027 cf028 cf029 cf030 cf031 cf032 cf033 cf034 cf035
       cf036 cf037 cf038 cf039 cf040 cf041 cf042 cf043 cf044 cf045 cf046 cf047
       cf048 cf049 cf050 cf051 cf052 cf053 cf054 cf055 cf056 cf057 cf058 cf059
       cf060 cf061 cf062 cf063 cf064 cf065 cf066 cf067 cf068 cf069 cf070 cf071
       cf072 cf073 cf074 cf075 cf076 cf077 cf078 cf079 cf080 cf081 cf082 cf083
       cf084 cf085 cf086 cf087 cf088 cf089 cf090 cf091 cf092 cf093 cf094 cf095
       cf096 cf097 cf098 cf099 cf100 cf101 cf102 cf103 cf104 cf105 cf106 cf107
       cf108 cf109 cf110 cf111 cf112 cf113 cf114 cf115 cf116 cf117 cf118 cf119
       cf120 cf121 cf122 cf123 cf124 cf125 cf126 cf127 cf128 cf129 cf130 cf131
       cf132 cf133 cf134 cf135 cf136 cf137 cf138 cf139 cf140 cf141 cf142 cf143
       cf144 cf145 cf146 cf147 cf148 cf149 cf150 cf151 cf152 cf153 cf154 cf155
       cf156 cf157 cf158 cf159 cf160 cf161 cf162 cf163 cf164 cf165 cf166 cf167
       cf168 cf169 cf170 cf171 cf172 cf173 cf174 cf175 cf176 cf177 cf178 cf179
       cf180 cf181 cf182 cf183 cf184 cf185 cf186 cf187 cf188 cf189 cf190 cf191
       cf192 cf193 cf194 cf195 cf196 cf197 cf198 cf199 cf200 cf201 cf202 cf203
       cf204 cf205 cf206 cf207 cf208 cf209 cf210 cf211 cf212 cf213 cf214 cf215
       cf216 cf217 cf218 cf219 cf220 cf221 cf222 cf223 cf224 cf225 cf226 cf227
       cf228 cf229 cf230 cf231 cf232 cf233 cf234 cf235 cf236 cf237 cf238 cf239
       cf240 cf241 cf242 cf243 cf244 cf245 cf246 cf247 cf248 cf249 cf250 cf251
       cf252 cf253 cf254 cf255 cf256 cf257 cf258 cf259 cf260 cf261 cf262 cf263
       cf264 cf265 cf266 cf267 cf268 cf269 cf270 cf271 cf272 cf273 cf274 cf275
       cf276 cf277 cf278 cf279 cf280 cf281 cf282 cf283 cf284 cf285 cf286 cf287
       cf288 cf289 cf290 cf291 cf292 cf293 cf294 cf295 cf296 cf297 cf298 cf299
       cf300 cf301 cf302 cf303 cf304 cf305 cf306 cf307 cf308 cf309 cf310 cf311
       cf312 cf313 cf314 cf315 cf316 cf317 cf318 cf319 cf320 cf321 cf322 cf323
       cf324 cf325 cf326 cf327 cf328 cf329 cf330 cf331 cf332 cf333 cf334 cf335
       cf336 cf337 cf338 cf339 cf340 cf341 cf342 cf343 cf344 cf345 cf346 cf347
       cf348 cf349 cf350 cf351 cf352 cf353 cf354 cf355 cf356 cf357 cf358 cf359
       cf360 cf361 cf362 cf363 cf364 cf365 cf366 cf367 cf368 cf369 cf370 cf371
       cf372 cf373 cf374 cf375 cf376 cf377 cf378 cf379 cf380 cf381 cf382 cf383
       cf384 cf385 cf386 cf387 cf388 cf389 cf390 cf391 cf392 cf393 cf394 cf395
       cf396 cf397 cf398 cf399 cf400 cf401 cf402 cf403 cf404 cf405 cf406 cf407
       cf408 cf409 cf410 cf411 cf412 cf413 cf414 cf415 cf416 cf417 cf418 cf419
       cf420 cf421 cf422 cf423 cf424 cf425 cf426 cf427 cf428 cf429 cf430 cf431
       cf432 cf433 cf434 cf435 cf436 cf437 cf438 cf439 cf440 cf441 cf442 cf443
       cf444 cf445 cf446 cf447 cf448 cf449 cf450 cf451 cf452 cf453 cf454 cf455
       cf456 cf457 cf458 cf459 cf460 cf461 cf462 cf463 cf464 cf465 cf466 cf467
       cf468 cf469 cf470 cf471 cf472 cf473 cf474 cf475 cf476 cf477 cf478 cf479
       cf480 cf481 cf482 cf483 cf484 cf485 cf486 cf487 cf488 cf489 cf490 cf491
       cf492 cf493 cf494 cf495 cf496 cf497 cf498 cf499 cf500 cf501 cf502 cf503
       cf504 cf505 cf506 cf507 cf508 cf509 cf510 cf511 cf512 cf513 cf514 cf515
       cf516 cf517 cf518 cf519 cf520 cf521 cf522 cf523 cf524 cf525 cf526 cf527
       cf528 cf529 cf530 cf531 cf532 cf533 cf534 cf535 cf536 cf537 cf538 cf539
       cf540 cf541 cf542 cf543 cf544 cf545 cf546 cf547 cf548 cf549 cf550 cf551
       cf552 cf553 cf554 cf555 cf556 cf557 cf558 cf559 cf560 cf561 cf562 cf563
       cf564 cf565 cf566 cf567 cf568 cf569 cf570 cf571 cf572 cf573 cf574 cf575
       cf576 cf577 cf578 cf579 cf580 cf581 cf582 cf583 cf584 cf585 cf586 cf587
       cf588 cf589 cf590 cf591 cf592 cf593 cf594 cf595 cf596 cf597 cf598 cf599
       cf600 cf601 cf602 cf603 cf604 cf605 cf606 cf607 cf608 cf609 cf610 cf611
       cf612 cf613 cf614 cf615 cf616 cf617 cf618 cf619 cf620 cf621 cf622 cf623
       cf624 cf625 cf626 cf627 cf628 cf629 cf630 cf631 cf632 cf633).

