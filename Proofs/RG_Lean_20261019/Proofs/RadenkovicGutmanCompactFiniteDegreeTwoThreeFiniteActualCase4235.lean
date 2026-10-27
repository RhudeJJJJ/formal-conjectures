/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons84
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4235 : Family 9 := level9.get ⟨171,by decide⟩
def sourceMap4235 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![7,0,1,2,3,4,5,6,15,14,8,9,10,11,12,13] (sourceLabel 9 2 2 v)
def fusedMap4235 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4235_checked : acceptsGraphIso
    (source (graph core4235) (root 9) 2 2) DegreeTwoThreeSpectrum4757.graph sourceMap4235=true := by decide +kernel
theorem fusedMap4235_checked : acceptsGraphIso
    (fused (graph core4235) (root 9) 2 2) DegreeTwoThreeSpectrum3934.graph fusedMap4235=true := by decide +kernel
theorem certified4235 : Certified (graph core4235) (root 9) 2 2 :=
  of_native_maps core4235 DegreeTwoThreeSpectrum4757.graph DegreeTwoThreeSpectrum3934.graph
    sourceMap4235 fusedMap4235 sourceMap4235_checked fusedMap4235_checked
    DegreeTwoThreeFiniteComparisons.comparison4235
#print axioms sourceMap4235_checked
#print axioms fusedMap4235_checked
#print axioms certified4235
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
