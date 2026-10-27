/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons96
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4812 : Family 10 := level10.get ⟨1162,by decide⟩
def sourceMap4812 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap4812 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4812_checked : acceptsGraphIso
    (source (graph core4812) (root 10) 2 2) DegreeTwoThreeSpectrum7245.graph sourceMap4812=true := by decide +kernel
theorem fusedMap4812_checked : acceptsGraphIso
    (fused (graph core4812) (root 10) 2 2) DegreeTwoThreeSpectrum6308.graph fusedMap4812=true := by decide +kernel
theorem certified4812 : Certified (graph core4812) (root 10) 2 2 :=
  of_native_maps core4812 DegreeTwoThreeSpectrum7245.graph DegreeTwoThreeSpectrum6308.graph
    sourceMap4812 fusedMap4812 sourceMap4812_checked fusedMap4812_checked
    DegreeTwoThreeFiniteComparisons.comparison4812
#print axioms sourceMap4812_checked
#print axioms fusedMap4812_checked
#print axioms certified4812
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
