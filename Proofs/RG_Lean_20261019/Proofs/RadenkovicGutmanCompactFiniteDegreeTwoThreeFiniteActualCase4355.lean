/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons87
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4355 : Family 9 := level9.get ⟨489,by decide⟩
def sourceMap4355 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,9,10,11,12,13,14,15,7,8,1,2,3,4,5,6] (sourceLabel 9 2 2 v)
def fusedMap4355 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4355_checked : acceptsGraphIso
    (source (graph core4355) (root 9) 2 2) DegreeTwoThreeSpectrum4873.graph sourceMap4355=true := by decide +kernel
theorem fusedMap4355_checked : acceptsGraphIso
    (fused (graph core4355) (root 9) 2 2) DegreeTwoThreeSpectrum4559.graph fusedMap4355=true := by decide +kernel
theorem certified4355 : Certified (graph core4355) (root 9) 2 2 :=
  of_native_maps core4355 DegreeTwoThreeSpectrum4873.graph DegreeTwoThreeSpectrum4559.graph
    sourceMap4355 fusedMap4355 sourceMap4355_checked fusedMap4355_checked
    DegreeTwoThreeFiniteComparisons.comparison4355
#print axioms sourceMap4355_checked
#print axioms fusedMap4355_checked
#print axioms certified4355
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
