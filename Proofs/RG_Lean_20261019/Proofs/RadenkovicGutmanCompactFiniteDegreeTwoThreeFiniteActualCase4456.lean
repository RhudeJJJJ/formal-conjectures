/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons89
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4456 : Family 10 := level10.get ⟨130,by decide⟩
def sourceMap4456 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,1,0,10,11,12,13,14,15,16,9,3,4,5,6,7,8] (sourceLabel 10 2 2 v)
def fusedMap4456 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 2 2 v)
theorem sourceMap4456_checked : acceptsGraphIso
    (source (graph core4456) (root 10) 2 2) DegreeTwoThreeSpectrum6844.graph sourceMap4456=true := by decide +kernel
theorem fusedMap4456_checked : acceptsGraphIso
    (fused (graph core4456) (root 10) 2 2) DegreeTwoThreeSpectrum5059.graph fusedMap4456=true := by decide +kernel
theorem certified4456 : Certified (graph core4456) (root 10) 2 2 :=
  of_native_maps core4456 DegreeTwoThreeSpectrum6844.graph DegreeTwoThreeSpectrum5059.graph
    sourceMap4456 fusedMap4456 sourceMap4456_checked fusedMap4456_checked
    DegreeTwoThreeFiniteComparisons.comparison4456
#print axioms sourceMap4456_checked
#print axioms fusedMap4456_checked
#print axioms certified4456
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
