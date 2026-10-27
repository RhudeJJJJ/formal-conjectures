/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons85
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4259 : Family 9 := level9.get ⟨244,by decide⟩
def sourceMap4259 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![6,0,1,2,3,4,5,14,15,13,7,8,9,10,11,12] (sourceLabel 9 2 2 v)
def fusedMap4259 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4259_checked : acceptsGraphIso
    (source (graph core4259) (root 9) 2 2) DegreeTwoThreeSpectrum4860.graph sourceMap4259=true := by decide +kernel
theorem fusedMap4259_checked : acceptsGraphIso
    (fused (graph core4259) (root 9) 2 2) DegreeTwoThreeSpectrum4041.graph fusedMap4259=true := by decide +kernel
theorem certified4259 : Certified (graph core4259) (root 9) 2 2 :=
  of_native_maps core4259 DegreeTwoThreeSpectrum4860.graph DegreeTwoThreeSpectrum4041.graph
    sourceMap4259 fusedMap4259 sourceMap4259_checked fusedMap4259_checked
    DegreeTwoThreeFiniteComparisons.comparison4259
#print axioms sourceMap4259_checked
#print axioms fusedMap4259_checked
#print axioms certified4259
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
