/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons82
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4149 : Family 8 := level8.get ⟨168,by decide⟩
def sourceMap4149 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,8,9,10,11,12,13,14,7,1,2,3,4,5,6] (sourceLabel 8 2 2 v)
def fusedMap4149 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap4149_checked : acceptsGraphIso
    (source (graph core4149) (root 8) 2 2) DegreeTwoThreeSpectrum3623.graph sourceMap4149=true := by decide +kernel
theorem fusedMap4149_checked : acceptsGraphIso
    (fused (graph core4149) (root 8) 2 2) DegreeTwoThreeSpectrum2848.graph fusedMap4149=true := by decide +kernel
theorem certified4149 : Certified (graph core4149) (root 8) 2 2 :=
  of_native_maps core4149 DegreeTwoThreeSpectrum3623.graph DegreeTwoThreeSpectrum2848.graph
    sourceMap4149 fusedMap4149 sourceMap4149_checked fusedMap4149_checked
    DegreeTwoThreeFiniteComparisons.comparison4149
#print axioms sourceMap4149_checked
#print axioms fusedMap4149_checked
#print axioms certified4149
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
