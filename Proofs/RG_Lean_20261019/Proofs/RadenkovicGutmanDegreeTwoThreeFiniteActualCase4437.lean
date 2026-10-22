/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons88
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4437 : Family 10 := level10.get ⟨43,by decide⟩
def sourceMap4437 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,1,0,10,11,12,13,14,15,16,9,3,4,5,6,7,8] (sourceLabel 10 2 2 v)
def fusedMap4437 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 2 2 v)
theorem sourceMap4437_checked : acceptsGraphIso
    (source (graph core4437) (root 10) 2 2) DegreeTwoThreeSpectrum5660.graph sourceMap4437=true := by decide +kernel
theorem fusedMap4437_checked : acceptsGraphIso
    (fused (graph core4437) (root 10) 2 2) DegreeTwoThreeSpectrum5122.graph fusedMap4437=true := by decide +kernel
theorem certified4437 : Certified (graph core4437) (root 10) 2 2 :=
  of_native_maps core4437 DegreeTwoThreeSpectrum5660.graph DegreeTwoThreeSpectrum5122.graph
    sourceMap4437 fusedMap4437 sourceMap4437_checked fusedMap4437_checked
    DegreeTwoThreeFiniteComparisons.comparison4437
#print axioms sourceMap4437_checked
#print axioms fusedMap4437_checked
#print axioms certified4437
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
