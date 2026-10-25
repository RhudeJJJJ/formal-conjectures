# Graphical Bell proof development — INCOMPLETE
This branch develops a proof of the two unchanged endpoints in PR7385.
No full proof of coefficientwise or conjecture is claimed here.
The integer coefficient operator module is locally kernel-checked with Lean4.33.1,
warnings as errors, autoImplicit=false and relaxedAutoImplicit=false.
The actual-partition deletion, reconstruction and insertion modules are being checked.
The exact quasi-complete-candidate counting bridge and universal graph induction remain open.
BellBridge derives the Bell conclusion from the still-unproved coefficientwise input.
It is not itself a complete proof of either submitted endpoint.
The original source's admitted declarations must never be used as proof dependencies.
Only a later complete exact-type and transitive-axiom audit could justify formal_proof links.
