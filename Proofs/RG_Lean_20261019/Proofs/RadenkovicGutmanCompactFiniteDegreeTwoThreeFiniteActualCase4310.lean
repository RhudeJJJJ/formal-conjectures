/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons86
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4310 : Family 9 := level9.get ⟨380,by decide⟩
def sourceMap4310 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![7,0,1,2,3,4,5,6,14,15,8,9,10,11,12,13] (sourceLabel 9 2 2 v)
def fusedMap4310 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4310_checked : acceptsGraphIso
    (source (graph core4310) (root 9) 2 2) DegreeTwoThreeSpectrum4752.graph sourceMap4310=true := by decide +kernel
theorem fusedMap4310_checked : acceptsGraphIso
    (fused (graph core4310) (root 9) 2 2) DegreeTwoThreeSpectrum4317.graph fusedMap4310=true := by decide +kernel
theorem certified4310 : Certified (graph core4310) (root 9) 2 2 :=
  of_native_maps core4310 DegreeTwoThreeSpectrum4752.graph DegreeTwoThreeSpectrum4317.graph
    sourceMap4310 fusedMap4310 sourceMap4310_checked fusedMap4310_checked
    DegreeTwoThreeFiniteComparisons.comparison4310
#print axioms sourceMap4310_checked
#print axioms fusedMap4310_checked
#print axioms certified4310
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
