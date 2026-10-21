/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0158 : Family 4 := level4.get ⟨4,by decide⟩
def sourceMap0158 : (Vertices 4 ⊕ Fin 4 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,9,10,11,12,1,2,3,4,5,6,7,8] (sourceLabel 4 3 3 v)
def fusedMap0158 : (Vertices 4 ⊕ Fin 8) → Fin 13 :=
  fun v => ![3,4,5,6,7,2,1,0,8,9,10,11,12] (fusedLabel 4 3 3 v)
theorem sourceMap0158_checked : acceptsGraphIso
    (source (graph core0158) (root 4) 3 3) DegreeOneSmallSpectrum1512.graph sourceMap0158=true := by decide +kernel
theorem fusedMap0158_checked : acceptsGraphIso
    (fused (graph core0158) (root 4) 3 3) DegreeOneSmallSpectrum870.graph fusedMap0158=true := by decide +kernel
theorem certified0158 : Certified (graph core0158) (root 4) 3 3 :=
  of_native_maps core0158 DegreeOneSmallSpectrum1512.graph DegreeOneSmallSpectrum870.graph
    sourceMap0158 fusedMap0158 sourceMap0158_checked fusedMap0158_checked
    DegreeOneSmallComparisons.comparison0158
#print axioms sourceMap0158_checked
#print axioms fusedMap0158_checked
#print axioms certified0158
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
