/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons48
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2417 : Family 10 := level10.get ⟨1298,by decide⟩
def sourceMap2417 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,5,6,7,8,9,10,11,12,4,2,3] (sourceLabel 10 0 0 v)
def fusedMap2417 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap2417_checked : acceptsGraphIso
    (source (graph core2417) (root 10) 0 0) DegreeOneSmallSpectrum1824.graph sourceMap2417=true := by decide +kernel
theorem fusedMap2417_checked : acceptsGraphIso
    (fused (graph core2417) (root 10) 0 0) DegreeOneSmallSpectrum1936.graph fusedMap2417=true := by decide +kernel
theorem certified2417 : Certified (graph core2417) (root 10) 0 0 :=
  of_native_maps core2417 DegreeOneSmallSpectrum1824.graph DegreeOneSmallSpectrum1936.graph
    sourceMap2417 fusedMap2417 sourceMap2417_checked fusedMap2417_checked
    DegreeOneSmallComparisons.comparison2417
#print axioms sourceMap2417_checked
#print axioms fusedMap2417_checked
#print axioms certified2417
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
