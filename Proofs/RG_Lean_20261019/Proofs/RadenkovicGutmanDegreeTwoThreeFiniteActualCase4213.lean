/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons84
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4213 : Family 9 := level9.get ⟨98,by decide⟩
def sourceMap4213 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,0,9,10,11,12,13,14,15,8,2,3,4,5,6,7] (sourceLabel 9 2 2 v)
def fusedMap4213 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,9,10,11,12,13,14] (fusedLabel 9 2 2 v)
theorem sourceMap4213_checked : acceptsGraphIso
    (source (graph core4213) (root 9) 2 2) DegreeTwoThreeSpectrum4550.graph sourceMap4213=true := by decide +kernel
theorem fusedMap4213_checked : acceptsGraphIso
    (fused (graph core4213) (root 9) 2 2) DegreeTwoThreeSpectrum4080.graph fusedMap4213=true := by decide +kernel
theorem certified4213 : Certified (graph core4213) (root 9) 2 2 :=
  of_native_maps core4213 DegreeTwoThreeSpectrum4550.graph DegreeTwoThreeSpectrum4080.graph
    sourceMap4213 fusedMap4213 sourceMap4213_checked fusedMap4213_checked
    DegreeTwoThreeFiniteComparisons.comparison4213
#print axioms sourceMap4213_checked
#print axioms fusedMap4213_checked
#print axioms certified4213
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
