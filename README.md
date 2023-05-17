# meander

Meander is an UCI chess engine and a spiritual successor to Rodent.

It is also a test bed for evaluation features, the most prominent being

- pawn x pawn evaluation table, replacing doubled, defended and phalanx
  pawn evaluation and adding some more relations between remote pawns
- chosing piece/square tables according to pawn center type and castling status

What's the plan?
==

- tune the hell out of pawn x pawn table
- add bishop x pawn and knight x pawn table
- if it works, we have a good positional player