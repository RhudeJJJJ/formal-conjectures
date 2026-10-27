/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons89
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4478 : Family 10 := level10.get ⟨209,by decide⟩
def sourceMap4478 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4478 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 2 2 v)
theorem sourceMap4478_checked : acceptsGraphIso
    (source (graph core4478) (root 10) 2 2) DegreeTwoThreeSpectrum6165.graph sourceMap4478=true := by decide +kernel
theorem fusedMap4478_checked : acceptsGraphIso
    (fused (graph core4478) (root 10) 2 2) DegreeTwoThreeSpectrum5212.graph fusedMap4478=true := by decide +kernel
theorem certified4478 : Certified (graph core4478) (root 10) 2 2 :=
  of_native_maps core4478 DegreeTwoThreeSpectrum6165.graph DegreeTwoThreeSpectrum5212.graph
    sourceMap4478 fusedMap4478 sourceMap4478_checked fusedMap4478_checked
    DegreeTwoThreeFiniteComparisons.comparison4478
#print axioms sourceMap4478_checked
#print axioms fusedMap4478_checked
#print axioms certified4478
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
