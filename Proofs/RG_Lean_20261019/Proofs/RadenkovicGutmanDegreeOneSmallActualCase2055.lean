/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons41
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2055 : Family 10 := level10.get ⟨429,by decide⟩
def sourceMap2055 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,9,10,11,12,5,6,7,8,3,4] (sourceLabel 10 0 0 v)
def fusedMap2055 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,5,6,7,8,9,10,11,12,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap2055_checked : acceptsGraphIso
    (source (graph core2055) (root 10) 0 0) DegreeOneSmallSpectrum1183.graph sourceMap2055=true := by decide +kernel
theorem fusedMap2055_checked : acceptsGraphIso
    (fused (graph core2055) (root 10) 0 0) DegreeOneSmallSpectrum1509.graph fusedMap2055=true := by decide +kernel
theorem certified2055 : Certified (graph core2055) (root 10) 0 0 :=
  of_native_maps core2055 DegreeOneSmallSpectrum1183.graph DegreeOneSmallSpectrum1509.graph
    sourceMap2055 fusedMap2055 sourceMap2055_checked fusedMap2055_checked
    DegreeOneSmallComparisons.comparison2055
#print axioms sourceMap2055_checked
#print axioms fusedMap2055_checked
#print axioms certified2055
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
