/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons96
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4810 : Family 10 := level10.get ⟨1159,by decide⟩
def sourceMap4810 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4810 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4810_checked : acceptsGraphIso
    (source (graph core4810) (root 10) 2 2) DegreeTwoThreeSpectrum7242.graph sourceMap4810=true := by decide +kernel
theorem fusedMap4810_checked : acceptsGraphIso
    (fused (graph core4810) (root 10) 2 2) DegreeTwoThreeSpectrum6302.graph fusedMap4810=true := by decide +kernel
theorem certified4810 : Certified (graph core4810) (root 10) 2 2 :=
  of_native_maps core4810 DegreeTwoThreeSpectrum7242.graph DegreeTwoThreeSpectrum6302.graph
    sourceMap4810 fusedMap4810 sourceMap4810_checked fusedMap4810_checked
    DegreeTwoThreeFiniteComparisons.comparison4810
#print axioms sourceMap4810_checked
#print axioms fusedMap4810_checked
#print axioms certified4810
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
