/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons99
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4977 : Family 10 := level10.get ⟨1567,by decide⟩
def sourceMap4977 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4977 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4977_checked : acceptsGraphIso
    (source (graph core4977) (root 10) 2 2) DegreeTwoThreeSpectrum7578.graph sourceMap4977=true := by decide +kernel
theorem fusedMap4977_checked : acceptsGraphIso
    (fused (graph core4977) (root 10) 2 2) DegreeTwoThreeSpectrum6046.graph fusedMap4977=true := by decide +kernel
theorem certified4977 : Certified (graph core4977) (root 10) 2 2 :=
  of_native_maps core4977 DegreeTwoThreeSpectrum7578.graph DegreeTwoThreeSpectrum6046.graph
    sourceMap4977 fusedMap4977 sourceMap4977_checked fusedMap4977_checked
    DegreeTwoThreeFiniteComparisons.comparison4977
#print axioms sourceMap4977_checked
#print axioms fusedMap4977_checked
#print axioms certified4977
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
