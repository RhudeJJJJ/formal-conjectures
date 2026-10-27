/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons88
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4444 : Family 10 := level10.get ⟨77,by decide⟩
def sourceMap4444 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4444 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 2 2 v)
theorem sourceMap4444_checked : acceptsGraphIso
    (source (graph core4444) (root 10) 2 2) DegreeTwoThreeSpectrum6451.graph sourceMap4444=true := by decide +kernel
theorem fusedMap4444_checked : acceptsGraphIso
    (fused (graph core4444) (root 10) 2 2) DegreeTwoThreeSpectrum4992.graph fusedMap4444=true := by decide +kernel
theorem certified4444 : Certified (graph core4444) (root 10) 2 2 :=
  of_native_maps core4444 DegreeTwoThreeSpectrum6451.graph DegreeTwoThreeSpectrum4992.graph
    sourceMap4444 fusedMap4444 sourceMap4444_checked fusedMap4444_checked
    DegreeTwoThreeFiniteComparisons.comparison4444
#print axioms sourceMap4444_checked
#print axioms fusedMap4444_checked
#print axioms certified4444
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
