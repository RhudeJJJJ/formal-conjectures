/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons108
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5445 : Family 7 := level7.get ⟨79,by decide⟩
def sourceMap5445 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![4,0,1,2,3,5,6,7,8,9] (sourceLabel 7 0 0 v)
def fusedMap5445 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![4,0,1,2,3,5,6,9,7,8] (fusedLabel 7 0 0 v)
theorem sourceMap5445_checked : acceptsGraphIso
    (source (graph core5445) (root 7) 0 0) SmallGeFourSpectrum018.graph sourceMap5445=true := by decide +kernel
theorem fusedMap5445_checked : acceptsGraphIso
    (fused (graph core5445) (root 7) 0 0) DegreeOneSmallSpectrum123.graph fusedMap5445=true := by decide +kernel
theorem certified5445 : Certified (graph core5445) (root 7) 0 0 :=
  of_native_maps core5445 SmallGeFourSpectrum018.graph DegreeOneSmallSpectrum123.graph
    sourceMap5445 fusedMap5445 sourceMap5445_checked fusedMap5445_checked
    DegreeTwoThreeFiniteComparisons.comparison5445
#print axioms sourceMap5445_checked
#print axioms fusedMap5445_checked
#print axioms certified5445
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
