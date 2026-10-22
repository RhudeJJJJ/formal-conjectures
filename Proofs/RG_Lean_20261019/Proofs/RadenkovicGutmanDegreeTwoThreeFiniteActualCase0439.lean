/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0439 : Family 10 := level10.get ⟨183,by decide⟩
def sourceMap0439 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,7,3,4,5,6] (sourceLabel 10 0 0 v)
def fusedMap0439 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,7,3,4,5,6] (fusedLabel 10 0 0 v)
theorem sourceMap0439_checked : acceptsGraphIso
    (source (graph core0439) (root 10) 0 0) DegreeOneSmallSpectrum917.graph sourceMap0439=true := by decide +kernel
theorem fusedMap0439_checked : acceptsGraphIso
    (fused (graph core0439) (root 10) 0 0) DegreeOneSmallSpectrum910.graph fusedMap0439=true := by decide +kernel
theorem certified0439 : Certified (graph core0439) (root 10) 0 0 :=
  of_native_maps core0439 DegreeOneSmallSpectrum917.graph DegreeOneSmallSpectrum910.graph
    sourceMap0439 fusedMap0439 sourceMap0439_checked fusedMap0439_checked
    DegreeTwoThreeFiniteComparisons.comparison0439
#print axioms sourceMap0439_checked
#print axioms fusedMap0439_checked
#print axioms certified0439
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
