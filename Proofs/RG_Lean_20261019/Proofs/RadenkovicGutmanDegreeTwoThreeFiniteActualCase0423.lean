/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0423 : Family 10 := level10.get ⟨130,by decide⟩
def sourceMap0423 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,7,8,9,10,11,12,4,5,6] (sourceLabel 10 0 0 v)
def fusedMap0423 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,5,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap0423_checked : acceptsGraphIso
    (source (graph core0423) (root 10) 0 0) DegreeOneSmallSpectrum1079.graph sourceMap0423=true := by decide +kernel
theorem fusedMap0423_checked : acceptsGraphIso
    (fused (graph core0423) (root 10) 0 0) DegreeOneSmallSpectrum938.graph fusedMap0423=true := by decide +kernel
theorem certified0423 : Certified (graph core0423) (root 10) 0 0 :=
  of_native_maps core0423 DegreeOneSmallSpectrum1079.graph DegreeOneSmallSpectrum938.graph
    sourceMap0423 fusedMap0423 sourceMap0423_checked fusedMap0423_checked
    DegreeTwoThreeFiniteComparisons.comparison0423
#print axioms sourceMap0423_checked
#print axioms fusedMap0423_checked
#print axioms certified0423
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
