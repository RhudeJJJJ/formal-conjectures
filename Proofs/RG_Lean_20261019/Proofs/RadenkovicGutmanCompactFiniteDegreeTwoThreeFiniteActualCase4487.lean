/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons89
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4487 : Family 10 := level10.get ⟨245,by decide⟩
def sourceMap4487 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4487 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 2 2 v)
theorem sourceMap4487_checked : acceptsGraphIso
    (source (graph core4487) (root 10) 2 2) DegreeTwoThreeSpectrum6382.graph sourceMap4487=true := by decide +kernel
theorem fusedMap4487_checked : acceptsGraphIso
    (fused (graph core4487) (root 10) 2 2) DegreeTwoThreeSpectrum5327.graph fusedMap4487=true := by decide +kernel
theorem certified4487 : Certified (graph core4487) (root 10) 2 2 :=
  of_native_maps core4487 DegreeTwoThreeSpectrum6382.graph DegreeTwoThreeSpectrum5327.graph
    sourceMap4487 fusedMap4487 sourceMap4487_checked fusedMap4487_checked
    DegreeTwoThreeFiniteComparisons.comparison4487
#print axioms sourceMap4487_checked
#print axioms fusedMap4487_checked
#print axioms certified4487
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
