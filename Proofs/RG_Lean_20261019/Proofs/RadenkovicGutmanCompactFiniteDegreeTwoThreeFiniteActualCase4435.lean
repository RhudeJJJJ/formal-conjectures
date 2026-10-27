/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons88
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4435 : Family 10 := level10.get ⟨32,by decide⟩
def sourceMap4435 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,1,0,10,11,12,13,14,15,16,9,3,4,5,6,7,8] (sourceLabel 10 2 2 v)
def fusedMap4435 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 2 2 v)
theorem sourceMap4435_checked : acceptsGraphIso
    (source (graph core4435) (root 10) 2 2) DegreeTwoThreeSpectrum5658.graph sourceMap4435=true := by decide +kernel
theorem fusedMap4435_checked : acceptsGraphIso
    (fused (graph core4435) (root 10) 2 2) DegreeTwoThreeSpectrum5079.graph fusedMap4435=true := by decide +kernel
theorem certified4435 : Certified (graph core4435) (root 10) 2 2 :=
  of_native_maps core4435 DegreeTwoThreeSpectrum5658.graph DegreeTwoThreeSpectrum5079.graph
    sourceMap4435 fusedMap4435 sourceMap4435_checked fusedMap4435_checked
    DegreeTwoThreeFiniteComparisons.comparison4435
#print axioms sourceMap4435_checked
#print axioms fusedMap4435_checked
#print axioms certified4435
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
