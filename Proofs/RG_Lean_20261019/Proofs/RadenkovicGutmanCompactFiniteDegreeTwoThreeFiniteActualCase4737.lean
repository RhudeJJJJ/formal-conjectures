/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons94
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4737 : Family 10 := level10.get ⟨967,by decide⟩
def sourceMap4737 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,12,13,14,15,16,2,3,4,5,6,7,8,9,10,11] (sourceLabel 10 2 2 v)
def fusedMap4737 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4737_checked : acceptsGraphIso
    (source (graph core4737) (root 10) 2 2) DegreeTwoThreeSpectrum7273.graph sourceMap4737=true := by decide +kernel
theorem fusedMap4737_checked : acceptsGraphIso
    (fused (graph core4737) (root 10) 2 2) DegreeTwoThreeSpectrum5886.graph fusedMap4737=true := by decide +kernel
theorem certified4737 : Certified (graph core4737) (root 10) 2 2 :=
  of_native_maps core4737 DegreeTwoThreeSpectrum7273.graph DegreeTwoThreeSpectrum5886.graph
    sourceMap4737 fusedMap4737 sourceMap4737_checked fusedMap4737_checked
    DegreeTwoThreeFiniteComparisons.comparison4737
#print axioms sourceMap4737_checked
#print axioms fusedMap4737_checked
#print axioms certified4737
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
