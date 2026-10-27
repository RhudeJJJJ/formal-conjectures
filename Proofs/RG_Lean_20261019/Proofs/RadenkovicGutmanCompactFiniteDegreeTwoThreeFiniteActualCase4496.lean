/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons89
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4496 : Family 10 := level10.get ⟨275,by decide⟩
def sourceMap4496 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![7,6,0,1,2,3,4,5,15,16,14,8,9,10,11,12,13] (sourceLabel 10 2 2 v)
def fusedMap4496 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 2 2 v)
theorem sourceMap4496_checked : acceptsGraphIso
    (source (graph core4496) (root 10) 2 2) DegreeTwoThreeSpectrum6458.graph sourceMap4496=true := by decide +kernel
theorem fusedMap4496_checked : acceptsGraphIso
    (fused (graph core4496) (root 10) 2 2) DegreeTwoThreeSpectrum5406.graph fusedMap4496=true := by decide +kernel
theorem certified4496 : Certified (graph core4496) (root 10) 2 2 :=
  of_native_maps core4496 DegreeTwoThreeSpectrum6458.graph DegreeTwoThreeSpectrum5406.graph
    sourceMap4496 fusedMap4496 sourceMap4496_checked fusedMap4496_checked
    DegreeTwoThreeFiniteComparisons.comparison4496
#print axioms sourceMap4496_checked
#print axioms fusedMap4496_checked
#print axioms certified4496
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
