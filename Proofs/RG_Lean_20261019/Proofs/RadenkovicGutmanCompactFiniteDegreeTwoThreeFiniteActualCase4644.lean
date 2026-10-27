/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons92
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4644 : Family 10 := level10.get ⟨722,by decide⟩
def sourceMap4644 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![7,0,1,2,3,4,5,6,14,15,16,8,9,10,11,12,13] (sourceLabel 10 2 2 v)
def fusedMap4644 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4644_checked : acceptsGraphIso
    (source (graph core4644) (root 10) 2 2) DegreeTwoThreeSpectrum7373.graph sourceMap4644=true := by decide +kernel
theorem fusedMap4644_checked : acceptsGraphIso
    (fused (graph core4644) (root 10) 2 2) DegreeTwoThreeSpectrum5472.graph fusedMap4644=true := by decide +kernel
theorem certified4644 : Certified (graph core4644) (root 10) 2 2 :=
  of_native_maps core4644 DegreeTwoThreeSpectrum7373.graph DegreeTwoThreeSpectrum5472.graph
    sourceMap4644 fusedMap4644 sourceMap4644_checked fusedMap4644_checked
    DegreeTwoThreeFiniteComparisons.comparison4644
#print axioms sourceMap4644_checked
#print axioms fusedMap4644_checked
#print axioms certified4644
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
