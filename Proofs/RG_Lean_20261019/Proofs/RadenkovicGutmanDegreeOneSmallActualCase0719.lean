/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0719 : Family 7 := level7.get ⟨82,by decide⟩
def sourceMap0719 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,11,8,9,10] (sourceLabel 7 0 2 v)
def fusedMap0719 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 0 2 v)
theorem sourceMap0719_checked : acceptsGraphIso
    (source (graph core0719) (root 7) 0 2) SmallGeFourSpectrum173.graph sourceMap0719=true := by decide +kernel
theorem fusedMap0719_checked : acceptsGraphIso
    (fused (graph core0719) (root 7) 0 2) SmallGeFourSpectrum099.graph fusedMap0719=true := by decide +kernel
theorem certified0719 : Certified (graph core0719) (root 7) 0 2 :=
  of_native_maps core0719 SmallGeFourSpectrum173.graph SmallGeFourSpectrum099.graph
    sourceMap0719 fusedMap0719 sourceMap0719_checked fusedMap0719_checked
    DegreeOneSmallComparisons.comparison0719
#print axioms sourceMap0719_checked
#print axioms fusedMap0719_checked
#print axioms certified0719
def sourceMap0719swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 7 2 0 v)
def fusedMap0719swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 2 0 v)
theorem sourceMap0719swap_checked : acceptsGraphIso
    (source (graph core0719) (root 7) 2 0) SmallGeFourSpectrum173.graph sourceMap0719swap=true := by decide +kernel
theorem fusedMap0719swap_checked : acceptsGraphIso
    (fused (graph core0719) (root 7) 2 0) SmallGeFourSpectrum099.graph fusedMap0719swap=true := by decide +kernel
theorem certified0719swap : Certified (graph core0719) (root 7) 2 0 :=
  of_native_maps core0719 SmallGeFourSpectrum173.graph SmallGeFourSpectrum099.graph
    sourceMap0719swap fusedMap0719swap sourceMap0719swap_checked fusedMap0719swap_checked
    DegreeOneSmallComparisons.comparison0719
#print axioms sourceMap0719swap_checked
#print axioms fusedMap0719swap_checked
#print axioms certified0719swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
