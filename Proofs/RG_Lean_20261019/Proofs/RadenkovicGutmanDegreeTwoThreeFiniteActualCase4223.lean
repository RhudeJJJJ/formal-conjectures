/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons84
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4223 : Family 9 := level9.get ⟨130,by decide⟩
def sourceMap4223 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,0,11,12,13,14,15,9,10,8,2,3,4,5,6,7] (sourceLabel 9 2 2 v)
def fusedMap4223 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,9,10,11,12,13,14] (fusedLabel 9 2 2 v)
theorem sourceMap4223_checked : acceptsGraphIso
    (source (graph core4223) (root 9) 2 2) DegreeTwoThreeSpectrum4546.graph sourceMap4223=true := by decide +kernel
theorem fusedMap4223_checked : acceptsGraphIso
    (fused (graph core4223) (root 9) 2 2) DegreeTwoThreeSpectrum4165.graph fusedMap4223=true := by decide +kernel
theorem certified4223 : Certified (graph core4223) (root 9) 2 2 :=
  of_native_maps core4223 DegreeTwoThreeSpectrum4546.graph DegreeTwoThreeSpectrum4165.graph
    sourceMap4223 fusedMap4223 sourceMap4223_checked fusedMap4223_checked
    DegreeTwoThreeFiniteComparisons.comparison4223
#print axioms sourceMap4223_checked
#print axioms fusedMap4223_checked
#print axioms certified4223
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
