/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons84
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4217 : Family 9 := level9.get ⟨110,by decide⟩
def sourceMap4217 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,0,10,11,12,13,14,15,8,9,2,3,4,5,6,7] (sourceLabel 9 2 2 v)
def fusedMap4217 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,14,15,8,9,10,11,12,13] (fusedLabel 9 2 2 v)
theorem sourceMap4217_checked : acceptsGraphIso
    (source (graph core4217) (root 9) 2 2) DegreeTwoThreeSpectrum4542.graph sourceMap4217=true := by decide +kernel
theorem fusedMap4217_checked : acceptsGraphIso
    (fused (graph core4217) (root 9) 2 2) DegreeTwoThreeSpectrum4113.graph fusedMap4217=true := by decide +kernel
theorem certified4217 : Certified (graph core4217) (root 9) 2 2 :=
  of_native_maps core4217 DegreeTwoThreeSpectrum4542.graph DegreeTwoThreeSpectrum4113.graph
    sourceMap4217 fusedMap4217 sourceMap4217_checked fusedMap4217_checked
    DegreeTwoThreeFiniteComparisons.comparison4217
#print axioms sourceMap4217_checked
#print axioms fusedMap4217_checked
#print axioms certified4217
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
