/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons84
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4232 : Family 9 := level9.get ⟨160,by decide⟩
def sourceMap4232 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,9,10,11,12,13,14] (sourceLabel 9 2 2 v)
def fusedMap4232 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4232_checked : acceptsGraphIso
    (source (graph core4232) (root 9) 2 2) DegreeTwoThreeSpectrum4734.graph sourceMap4232=true := by decide +kernel
theorem fusedMap4232_checked : acceptsGraphIso
    (fused (graph core4232) (root 9) 2 2) DegreeTwoThreeSpectrum3921.graph fusedMap4232=true := by decide +kernel
theorem certified4232 : Certified (graph core4232) (root 9) 2 2 :=
  of_native_maps core4232 DegreeTwoThreeSpectrum4734.graph DegreeTwoThreeSpectrum3921.graph
    sourceMap4232 fusedMap4232 sourceMap4232_checked fusedMap4232_checked
    DegreeTwoThreeFiniteComparisons.comparison4232
#print axioms sourceMap4232_checked
#print axioms fusedMap4232_checked
#print axioms certified4232
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
