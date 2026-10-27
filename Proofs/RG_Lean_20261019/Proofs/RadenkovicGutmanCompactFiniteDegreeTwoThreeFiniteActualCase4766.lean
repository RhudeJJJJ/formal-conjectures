/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons95
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4766 : Family 10 := level10.get ⟨1047,by decide⟩
def sourceMap4766 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4766 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4766_checked : acceptsGraphIso
    (source (graph core4766) (root 10) 2 2) DegreeTwoThreeSpectrum7124.graph sourceMap4766=true := by decide +kernel
theorem fusedMap4766_checked : acceptsGraphIso
    (fused (graph core4766) (root 10) 2 2) DegreeTwoThreeSpectrum6078.graph fusedMap4766=true := by decide +kernel
theorem certified4766 : Certified (graph core4766) (root 10) 2 2 :=
  of_native_maps core4766 DegreeTwoThreeSpectrum7124.graph DegreeTwoThreeSpectrum6078.graph
    sourceMap4766 fusedMap4766 sourceMap4766_checked fusedMap4766_checked
    DegreeTwoThreeFiniteComparisons.comparison4766
#print axioms sourceMap4766_checked
#print axioms fusedMap4766_checked
#print axioms certified4766
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
