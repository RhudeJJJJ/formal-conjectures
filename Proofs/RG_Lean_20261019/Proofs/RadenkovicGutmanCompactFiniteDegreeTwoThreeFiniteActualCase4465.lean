/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons89
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4465 : Family 10 := level10.get ⟨162,by decide⟩
def sourceMap4465 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,1,0,11,12,13,14,15,16,9,10,3,4,5,6,7,8] (sourceLabel 10 2 2 v)
def fusedMap4465 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,16,9,10,11,12,13,14] (fusedLabel 10 2 2 v)
theorem sourceMap4465_checked : acceptsGraphIso
    (source (graph core4465) (root 10) 2 2) DegreeTwoThreeSpectrum6815.graph sourceMap4465=true := by decide +kernel
theorem fusedMap4465_checked : acceptsGraphIso
    (fused (graph core4465) (root 10) 2 2) DegreeTwoThreeSpectrum5102.graph fusedMap4465=true := by decide +kernel
theorem certified4465 : Certified (graph core4465) (root 10) 2 2 :=
  of_native_maps core4465 DegreeTwoThreeSpectrum6815.graph DegreeTwoThreeSpectrum5102.graph
    sourceMap4465 fusedMap4465 sourceMap4465_checked fusedMap4465_checked
    DegreeTwoThreeFiniteComparisons.comparison4465
#print axioms sourceMap4465_checked
#print axioms fusedMap4465_checked
#print axioms certified4465
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
