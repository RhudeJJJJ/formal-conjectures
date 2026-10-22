/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons84
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4245 : Family 9 := level9.get ⟨196,by decide⟩
def sourceMap4245 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![6,0,1,2,3,4,5,13,14,15,7,8,9,10,11,12] (sourceLabel 9 2 2 v)
def fusedMap4245 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4245_checked : acceptsGraphIso
    (source (graph core4245) (root 9) 2 2) DegreeTwoThreeSpectrum4784.graph sourceMap4245=true := by decide +kernel
theorem fusedMap4245_checked : acceptsGraphIso
    (fused (graph core4245) (root 9) 2 2) DegreeTwoThreeSpectrum3972.graph fusedMap4245=true := by decide +kernel
theorem certified4245 : Certified (graph core4245) (root 9) 2 2 :=
  of_native_maps core4245 DegreeTwoThreeSpectrum4784.graph DegreeTwoThreeSpectrum3972.graph
    sourceMap4245 fusedMap4245 sourceMap4245_checked fusedMap4245_checked
    DegreeTwoThreeFiniteComparisons.comparison4245
#print axioms sourceMap4245_checked
#print axioms fusedMap4245_checked
#print axioms certified4245
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
