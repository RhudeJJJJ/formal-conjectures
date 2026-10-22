/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons90
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4540 : Family 10 := level10.get ⟨421,by decide⟩
def sourceMap4540 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,11,12,13,14,15,16,9,10,8,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap4540 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 2 2 v)
theorem sourceMap4540_checked : acceptsGraphIso
    (source (graph core4540) (root 10) 2 2) DegreeTwoThreeSpectrum6826.graph sourceMap4540=true := by decide +kernel
theorem fusedMap4540_checked : acceptsGraphIso
    (fused (graph core4540) (root 10) 2 2) DegreeTwoThreeSpectrum5806.graph fusedMap4540=true := by decide +kernel
theorem certified4540 : Certified (graph core4540) (root 10) 2 2 :=
  of_native_maps core4540 DegreeTwoThreeSpectrum6826.graph DegreeTwoThreeSpectrum5806.graph
    sourceMap4540 fusedMap4540 sourceMap4540_checked fusedMap4540_checked
    DegreeTwoThreeFiniteComparisons.comparison4540
#print axioms sourceMap4540_checked
#print axioms fusedMap4540_checked
#print axioms certified4540
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
