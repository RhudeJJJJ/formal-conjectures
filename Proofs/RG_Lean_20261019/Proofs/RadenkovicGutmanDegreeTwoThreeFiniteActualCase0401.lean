/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0401 : Family 10 := level10.get ⟨25,by decide⟩
def sourceMap0401 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,7,8,9,10,11,12,4,5,6] (sourceLabel 10 0 0 v)
def fusedMap0401 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![3,2,1,0,7,8,9,10,11,12,6,4,5] (fusedLabel 10 0 0 v)
theorem sourceMap0401_checked : acceptsGraphIso
    (source (graph core0401) (root 10) 0 0) DegreeOneSmallSpectrum867.graph sourceMap0401=true := by decide +kernel
theorem fusedMap0401_checked : acceptsGraphIso
    (fused (graph core0401) (root 10) 0 0) DegreeOneSmallSpectrum936.graph fusedMap0401=true := by decide +kernel
theorem certified0401 : Certified (graph core0401) (root 10) 0 0 :=
  of_native_maps core0401 DegreeOneSmallSpectrum867.graph DegreeOneSmallSpectrum936.graph
    sourceMap0401 fusedMap0401 sourceMap0401_checked fusedMap0401_checked
    DegreeTwoThreeFiniteComparisons.comparison0401
#print axioms sourceMap0401_checked
#print axioms fusedMap0401_checked
#print axioms certified0401
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
