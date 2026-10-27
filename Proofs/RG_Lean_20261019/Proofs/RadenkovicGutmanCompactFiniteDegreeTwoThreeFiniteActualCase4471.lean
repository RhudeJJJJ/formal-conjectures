/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons89
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4471 : Family 10 := level10.get ⟨182,by decide⟩
def sourceMap4471 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,1,0,12,13,14,15,16,10,11,9,3,4,5,6,7,8] (sourceLabel 10 2 2 v)
def fusedMap4471 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 2 2 v)
theorem sourceMap4471_checked : acceptsGraphIso
    (source (graph core4471) (root 10) 2 2) DegreeTwoThreeSpectrum6828.graph sourceMap4471=true := by decide +kernel
theorem fusedMap4471_checked : acceptsGraphIso
    (fused (graph core4471) (root 10) 2 2) DegreeTwoThreeSpectrum5129.graph fusedMap4471=true := by decide +kernel
theorem certified4471 : Certified (graph core4471) (root 10) 2 2 :=
  of_native_maps core4471 DegreeTwoThreeSpectrum6828.graph DegreeTwoThreeSpectrum5129.graph
    sourceMap4471 fusedMap4471 sourceMap4471_checked fusedMap4471_checked
    DegreeTwoThreeFiniteComparisons.comparison4471
#print axioms sourceMap4471_checked
#print axioms fusedMap4471_checked
#print axioms certified4471
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
