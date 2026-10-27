/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons83
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4182 : Family 8 := level8.get ⟨241,by decide⟩
def sourceMap4182 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,14,8,9,10,11,12,13] (sourceLabel 8 2 2 v)
def fusedMap4182 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap4182_checked : acceptsGraphIso
    (source (graph core4182) (root 8) 2 2) DegreeTwoThreeSpectrum3837.graph sourceMap4182=true := by decide +kernel
theorem fusedMap4182_checked : acceptsGraphIso
    (fused (graph core4182) (root 8) 2 2) DegreeTwoThreeSpectrum2690.graph fusedMap4182=true := by decide +kernel
theorem certified4182 : Certified (graph core4182) (root 8) 2 2 :=
  of_native_maps core4182 DegreeTwoThreeSpectrum3837.graph DegreeTwoThreeSpectrum2690.graph
    sourceMap4182 fusedMap4182 sourceMap4182_checked fusedMap4182_checked
    DegreeTwoThreeFiniteComparisons.comparison4182
#print axioms sourceMap4182_checked
#print axioms fusedMap4182_checked
#print axioms certified4182
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
