/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons87
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4362 : Family 9 := level9.get ⟨505,by decide⟩
def sourceMap4362 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,10,11,12,13,14,15,1,2,3,4,5,6,7,8,9] (sourceLabel 9 2 2 v)
def fusedMap4362 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4362_checked : acceptsGraphIso
    (source (graph core4362) (root 9) 2 2) DegreeTwoThreeSpectrum4862.graph sourceMap4362=true := by decide +kernel
theorem fusedMap4362_checked : acceptsGraphIso
    (fused (graph core4362) (root 9) 2 2) DegreeTwoThreeSpectrum4586.graph fusedMap4362=true := by decide +kernel
theorem certified4362 : Certified (graph core4362) (root 9) 2 2 :=
  of_native_maps core4362 DegreeTwoThreeSpectrum4862.graph DegreeTwoThreeSpectrum4586.graph
    sourceMap4362 fusedMap4362 sourceMap4362_checked fusedMap4362_checked
    DegreeTwoThreeFiniteComparisons.comparison4362
#print axioms sourceMap4362_checked
#print axioms fusedMap4362_checked
#print axioms certified4362
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
