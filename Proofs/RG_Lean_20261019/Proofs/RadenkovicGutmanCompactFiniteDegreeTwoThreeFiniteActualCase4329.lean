/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons86
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4329 : Family 9 := level9.get ⟨429,by decide⟩
def sourceMap4329 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,9,10,11,12,13,14] (sourceLabel 9 2 2 v)
def fusedMap4329 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4329_checked : acceptsGraphIso
    (source (graph core4329) (root 9) 2 2) DegreeTwoThreeSpectrum4806.graph sourceMap4329=true := by decide +kernel
theorem fusedMap4329_checked : acceptsGraphIso
    (fused (graph core4329) (root 9) 2 2) DegreeTwoThreeSpectrum4423.graph fusedMap4329=true := by decide +kernel
theorem certified4329 : Certified (graph core4329) (root 9) 2 2 :=
  of_native_maps core4329 DegreeTwoThreeSpectrum4806.graph DegreeTwoThreeSpectrum4423.graph
    sourceMap4329 fusedMap4329 sourceMap4329_checked fusedMap4329_checked
    DegreeTwoThreeFiniteComparisons.comparison4329
#print axioms sourceMap4329_checked
#print axioms fusedMap4329_checked
#print axioms certified4329
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
