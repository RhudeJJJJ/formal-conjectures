/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons96
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4835 : Family 10 := level10.get ⟨1213,by decide⟩
def sourceMap4835 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,11,12,13,14,15,16,1,2,3,4,5,6,7,8,9,10] (sourceLabel 10 2 2 v)
def fusedMap4835 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4835_checked : acceptsGraphIso
    (source (graph core4835) (root 10) 2 2) DegreeTwoThreeSpectrum7264.graph sourceMap4835=true := by decide +kernel
theorem fusedMap4835_checked : acceptsGraphIso
    (fused (graph core4835) (root 10) 2 2) DegreeTwoThreeSpectrum6401.graph fusedMap4835=true := by decide +kernel
theorem certified4835 : Certified (graph core4835) (root 10) 2 2 :=
  of_native_maps core4835 DegreeTwoThreeSpectrum7264.graph DegreeTwoThreeSpectrum6401.graph
    sourceMap4835 fusedMap4835 sourceMap4835_checked fusedMap4835_checked
    DegreeTwoThreeFiniteComparisons.comparison4835
#print axioms sourceMap4835_checked
#print axioms fusedMap4835_checked
#print axioms certified4835
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
