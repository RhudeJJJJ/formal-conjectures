/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0981 : Family 10 := level10.get ⟨1651,by decide⟩
def sourceMap0981 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0981 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,6,7,8,9,10,11,12,1,2,3,4,5] (fusedLabel 10 0 0 v)
theorem sourceMap0981_checked : acceptsGraphIso
    (source (graph core0981) (root 10) 0 0) DegreeOneSmallSpectrum1784.graph sourceMap0981=true := by decide +kernel
theorem fusedMap0981_checked : acceptsGraphIso
    (fused (graph core0981) (root 10) 0 0) DegreeOneSmallSpectrum1756.graph fusedMap0981=true := by decide +kernel
theorem certified0981 : Certified (graph core0981) (root 10) 0 0 :=
  of_native_maps core0981 DegreeOneSmallSpectrum1784.graph DegreeOneSmallSpectrum1756.graph
    sourceMap0981 fusedMap0981 sourceMap0981_checked fusedMap0981_checked
    DegreeTwoThreeFiniteComparisons.comparison0981
#print axioms sourceMap0981_checked
#print axioms fusedMap0981_checked
#print axioms certified0981
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
