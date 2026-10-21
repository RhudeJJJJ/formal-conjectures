/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1055 : Family 8 := level8.get ⟨124,by decide⟩
def sourceMap1055 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,0,7,8,9,10,4,5,6,2,3] (sourceLabel 8 0 0 v)
def fusedMap1055 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![5,0,1,2,3,4,8,9,10,6,7] (fusedLabel 8 0 0 v)
theorem sourceMap1055_checked : acceptsGraphIso
    (source (graph core1055) (root 8) 0 0) DegreeOneSmallSpectrum283.graph sourceMap1055=true := by decide +kernel
theorem fusedMap1055_checked : acceptsGraphIso
    (fused (graph core1055) (root 8) 0 0) SmallGeFourSpectrum054.graph fusedMap1055=true := by decide +kernel
theorem certified1055 : Certified (graph core1055) (root 8) 0 0 :=
  of_native_maps core1055 DegreeOneSmallSpectrum283.graph SmallGeFourSpectrum054.graph
    sourceMap1055 fusedMap1055 sourceMap1055_checked fusedMap1055_checked
    DegreeOneSmallComparisons.comparison1055
#print axioms sourceMap1055_checked
#print axioms fusedMap1055_checked
#print axioms certified1055
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
