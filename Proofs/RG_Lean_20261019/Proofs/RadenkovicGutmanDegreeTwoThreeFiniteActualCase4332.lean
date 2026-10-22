/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons86
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4332 : Family 9 := level9.get ⟨434,by decide⟩
def sourceMap4332 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap4332 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4332_checked : acceptsGraphIso
    (source (graph core4332) (root 9) 2 2) DegreeTwoThreeSpectrum4810.graph sourceMap4332=true := by decide +kernel
theorem fusedMap4332_checked : acceptsGraphIso
    (fused (graph core4332) (root 9) 2 2) DegreeTwoThreeSpectrum4431.graph fusedMap4332=true := by decide +kernel
theorem certified4332 : Certified (graph core4332) (root 9) 2 2 :=
  of_native_maps core4332 DegreeTwoThreeSpectrum4810.graph DegreeTwoThreeSpectrum4431.graph
    sourceMap4332 fusedMap4332 sourceMap4332_checked fusedMap4332_checked
    DegreeTwoThreeFiniteComparisons.comparison4332
#print axioms sourceMap4332_checked
#print axioms fusedMap4332_checked
#print axioms certified4332
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
