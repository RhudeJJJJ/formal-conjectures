/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons84
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4239 : Family 9 := level9.get ⟨184,by decide⟩
def sourceMap4239 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![7,0,1,2,3,4,5,6,15,14,8,9,10,11,12,13] (sourceLabel 9 2 2 v)
def fusedMap4239 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4239_checked : acceptsGraphIso
    (source (graph core4239) (root 9) 2 2) DegreeTwoThreeSpectrum4780.graph sourceMap4239=true := by decide +kernel
theorem fusedMap4239_checked : acceptsGraphIso
    (fused (graph core4239) (root 9) 2 2) DegreeTwoThreeSpectrum3952.graph fusedMap4239=true := by decide +kernel
theorem certified4239 : Certified (graph core4239) (root 9) 2 2 :=
  of_native_maps core4239 DegreeTwoThreeSpectrum4780.graph DegreeTwoThreeSpectrum3952.graph
    sourceMap4239 fusedMap4239 sourceMap4239_checked fusedMap4239_checked
    DegreeTwoThreeFiniteComparisons.comparison4239
#print axioms sourceMap4239_checked
#print axioms fusedMap4239_checked
#print axioms certified4239
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
