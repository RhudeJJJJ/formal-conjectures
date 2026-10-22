/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons96
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4822 : Family 10 := level10.get ⟨1188,by decide⟩
def sourceMap4822 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4822 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4822_checked : acceptsGraphIso
    (source (graph core4822) (root 10) 2 2) DegreeTwoThreeSpectrum7279.graph sourceMap4822=true := by decide +kernel
theorem fusedMap4822_checked : acceptsGraphIso
    (fused (graph core4822) (root 10) 2 2) DegreeTwoThreeSpectrum6361.graph fusedMap4822=true := by decide +kernel
theorem certified4822 : Certified (graph core4822) (root 10) 2 2 :=
  of_native_maps core4822 DegreeTwoThreeSpectrum7279.graph DegreeTwoThreeSpectrum6361.graph
    sourceMap4822 fusedMap4822 sourceMap4822_checked fusedMap4822_checked
    DegreeTwoThreeFiniteComparisons.comparison4822
#print axioms sourceMap4822_checked
#print axioms fusedMap4822_checked
#print axioms certified4822
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
