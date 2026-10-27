/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons84
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4219 : Family 9 := level9.get ⟨119,by decide⟩
def sourceMap4219 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,0,9,10,11,12,13,14,15,8,2,3,4,5,6,7] (sourceLabel 9 2 2 v)
def fusedMap4219 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,9,10,11,12,13,14] (fusedLabel 9 2 2 v)
theorem sourceMap4219_checked : acceptsGraphIso
    (source (graph core4219) (root 9) 2 2) DegreeTwoThreeSpectrum4555.graph sourceMap4219=true := by decide +kernel
theorem fusedMap4219_checked : acceptsGraphIso
    (fused (graph core4219) (root 9) 2 2) DegreeTwoThreeSpectrum4138.graph fusedMap4219=true := by decide +kernel
theorem certified4219 : Certified (graph core4219) (root 9) 2 2 :=
  of_native_maps core4219 DegreeTwoThreeSpectrum4555.graph DegreeTwoThreeSpectrum4138.graph
    sourceMap4219 fusedMap4219 sourceMap4219_checked fusedMap4219_checked
    DegreeTwoThreeFiniteComparisons.comparison4219
#print axioms sourceMap4219_checked
#print axioms fusedMap4219_checked
#print axioms certified4219
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
