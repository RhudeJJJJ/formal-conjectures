/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons41
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2060 : Family 10 := level10.get ⟨435,by decide⟩
def sourceMap2060 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,9,10,11,12,5,6,7,8,3,4] (sourceLabel 10 0 0 v)
def fusedMap2060 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,5,6,7,8,9,10,11,12,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap2060_checked : acceptsGraphIso
    (source (graph core2060) (root 10) 0 0) DegreeOneSmallSpectrum1191.graph sourceMap2060=true := by decide +kernel
theorem fusedMap2060_checked : acceptsGraphIso
    (fused (graph core2060) (root 10) 0 0) DegreeOneSmallSpectrum1513.graph fusedMap2060=true := by decide +kernel
theorem certified2060 : Certified (graph core2060) (root 10) 0 0 :=
  of_native_maps core2060 DegreeOneSmallSpectrum1191.graph DegreeOneSmallSpectrum1513.graph
    sourceMap2060 fusedMap2060 sourceMap2060_checked fusedMap2060_checked
    DegreeOneSmallComparisons.comparison2060
#print axioms sourceMap2060_checked
#print axioms fusedMap2060_checked
#print axioms certified2060
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
