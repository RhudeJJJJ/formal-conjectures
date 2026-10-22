/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons89
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4459 : Family 10 := level10.get ⟨142,by decide⟩
def sourceMap4459 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,1,0,11,12,13,14,15,16,10,9,3,4,5,6,7,8] (sourceLabel 10 2 2 v)
def fusedMap4459 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 2 2 v)
theorem sourceMap4459_checked : acceptsGraphIso
    (source (graph core4459) (root 10) 2 2) DegreeTwoThreeSpectrum6832.graph sourceMap4459=true := by decide +kernel
theorem fusedMap4459_checked : acceptsGraphIso
    (fused (graph core4459) (root 10) 2 2) DegreeTwoThreeSpectrum5074.graph fusedMap4459=true := by decide +kernel
theorem certified4459 : Certified (graph core4459) (root 10) 2 2 :=
  of_native_maps core4459 DegreeTwoThreeSpectrum6832.graph DegreeTwoThreeSpectrum5074.graph
    sourceMap4459 fusedMap4459 sourceMap4459_checked fusedMap4459_checked
    DegreeTwoThreeFiniteComparisons.comparison4459
#print axioms sourceMap4459_checked
#print axioms fusedMap4459_checked
#print axioms certified4459
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
