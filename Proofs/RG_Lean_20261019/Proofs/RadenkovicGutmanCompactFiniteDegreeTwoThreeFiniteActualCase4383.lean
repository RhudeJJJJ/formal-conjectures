/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons87
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4383 : Family 9 := level9.get ⟨557,by decide⟩
def sourceMap4383 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap4383 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4383_checked : acceptsGraphIso
    (source (graph core4383) (root 9) 2 2) DegreeTwoThreeSpectrum4910.graph sourceMap4383=true := by decide +kernel
theorem fusedMap4383_checked : acceptsGraphIso
    (fused (graph core4383) (root 9) 2 2) DegreeTwoThreeSpectrum4193.graph fusedMap4383=true := by decide +kernel
theorem certified4383 : Certified (graph core4383) (root 9) 2 2 :=
  of_native_maps core4383 DegreeTwoThreeSpectrum4910.graph DegreeTwoThreeSpectrum4193.graph
    sourceMap4383 fusedMap4383 sourceMap4383_checked fusedMap4383_checked
    DegreeTwoThreeFiniteComparisons.comparison4383
#print axioms sourceMap4383_checked
#print axioms fusedMap4383_checked
#print axioms certified4383
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
