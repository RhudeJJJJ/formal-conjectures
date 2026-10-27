/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons87
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4363 : Family 9 := level9.get ⟨506,by decide⟩
def sourceMap4363 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,10,11,12,13,14,15,7,8,9,1,2,3,4,5,6] (sourceLabel 9 2 2 v)
def fusedMap4363 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4363_checked : acceptsGraphIso
    (source (graph core4363) (root 9) 2 2) DegreeTwoThreeSpectrum4869.graph sourceMap4363=true := by decide +kernel
theorem fusedMap4363_checked : acceptsGraphIso
    (fused (graph core4363) (root 9) 2 2) DegreeTwoThreeSpectrum4588.graph fusedMap4363=true := by decide +kernel
theorem certified4363 : Certified (graph core4363) (root 9) 2 2 :=
  of_native_maps core4363 DegreeTwoThreeSpectrum4869.graph DegreeTwoThreeSpectrum4588.graph
    sourceMap4363 fusedMap4363 sourceMap4363_checked fusedMap4363_checked
    DegreeTwoThreeFiniteComparisons.comparison4363
#print axioms sourceMap4363_checked
#print axioms fusedMap4363_checked
#print axioms certified4363
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
