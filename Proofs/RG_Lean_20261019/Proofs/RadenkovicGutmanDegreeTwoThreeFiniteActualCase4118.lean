/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons82
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4118 : Family 8 := level8.get ⟨86,by decide⟩
def sourceMap4118 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,9,10,11,12,13,14,8,2,3,4,5,6,7] (sourceLabel 8 2 2 v)
def fusedMap4118 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap4118_checked : acceptsGraphIso
    (source (graph core4118) (root 8) 2 2) DegreeTwoThreeSpectrum3628.graph sourceMap4118=true := by decide +kernel
theorem fusedMap4118_checked : acceptsGraphIso
    (fused (graph core4118) (root 8) 2 2) DegreeTwoThreeSpectrum2411.graph fusedMap4118=true := by decide +kernel
theorem certified4118 : Certified (graph core4118) (root 8) 2 2 :=
  of_native_maps core4118 DegreeTwoThreeSpectrum3628.graph DegreeTwoThreeSpectrum2411.graph
    sourceMap4118 fusedMap4118 sourceMap4118_checked fusedMap4118_checked
    DegreeTwoThreeFiniteComparisons.comparison4118
#print axioms sourceMap4118_checked
#print axioms fusedMap4118_checked
#print axioms certified4118
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
