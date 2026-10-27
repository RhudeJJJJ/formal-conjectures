/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons96
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4833 : Family 10 := level10.get ⟨1209,by decide⟩
def sourceMap4833 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![7,0,1,2,3,4,5,6,14,15,16,8,9,10,11,12,13] (sourceLabel 10 2 2 v)
def fusedMap4833 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4833_checked : acceptsGraphIso
    (source (graph core4833) (root 10) 2 2) DegreeTwoThreeSpectrum7295.graph sourceMap4833=true := by decide +kernel
theorem fusedMap4833_checked : acceptsGraphIso
    (fused (graph core4833) (root 10) 2 2) DegreeTwoThreeSpectrum6393.graph fusedMap4833=true := by decide +kernel
theorem certified4833 : Certified (graph core4833) (root 10) 2 2 :=
  of_native_maps core4833 DegreeTwoThreeSpectrum7295.graph DegreeTwoThreeSpectrum6393.graph
    sourceMap4833 fusedMap4833 sourceMap4833_checked fusedMap4833_checked
    DegreeTwoThreeFiniteComparisons.comparison4833
#print axioms sourceMap4833_checked
#print axioms fusedMap4833_checked
#print axioms certified4833
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
