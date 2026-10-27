/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons88
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4417 : Family 9 := level9.get ⟨639,by decide⟩
def sourceMap4417 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,13,14,15,7,8,9,10,11,12] (sourceLabel 9 2 2 v)
def fusedMap4417 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4417_checked : acceptsGraphIso
    (source (graph core4417) (root 9) 2 2) DegreeTwoThreeSpectrum4944.graph sourceMap4417=true := by decide +kernel
theorem fusedMap4417_checked : acceptsGraphIso
    (fused (graph core4417) (root 9) 2 2) DegreeTwoThreeSpectrum4404.graph fusedMap4417=true := by decide +kernel
theorem certified4417 : Certified (graph core4417) (root 9) 2 2 :=
  of_native_maps core4417 DegreeTwoThreeSpectrum4944.graph DegreeTwoThreeSpectrum4404.graph
    sourceMap4417 fusedMap4417 sourceMap4417_checked fusedMap4417_checked
    DegreeTwoThreeFiniteComparisons.comparison4417
#print axioms sourceMap4417_checked
#print axioms fusedMap4417_checked
#print axioms certified4417
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
