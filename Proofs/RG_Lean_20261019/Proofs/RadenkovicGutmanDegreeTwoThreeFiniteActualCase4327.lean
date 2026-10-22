/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons86
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4327 : Family 9 := level9.get ⟨423,by decide⟩
def sourceMap4327 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,9,10,11,12,13,14] (sourceLabel 9 2 2 v)
def fusedMap4327 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4327_checked : acceptsGraphIso
    (source (graph core4327) (root 9) 2 2) DegreeTwoThreeSpectrum4798.graph sourceMap4327=true := by decide +kernel
theorem fusedMap4327_checked : acceptsGraphIso
    (fused (graph core4327) (root 9) 2 2) DegreeTwoThreeSpectrum4409.graph fusedMap4327=true := by decide +kernel
theorem certified4327 : Certified (graph core4327) (root 9) 2 2 :=
  of_native_maps core4327 DegreeTwoThreeSpectrum4798.graph DegreeTwoThreeSpectrum4409.graph
    sourceMap4327 fusedMap4327 sourceMap4327_checked fusedMap4327_checked
    DegreeTwoThreeFiniteComparisons.comparison4327
#print axioms sourceMap4327_checked
#print axioms fusedMap4327_checked
#print axioms certified4327
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
